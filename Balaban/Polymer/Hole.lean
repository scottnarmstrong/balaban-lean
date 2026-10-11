module

public import Balaban.Polymer.Sized
public import Balaban.Polymer.Support
public import Balaban.Polymer.Animals

/-!
# The polymer expansion with a hole and the Steiner size

POLYMER.md §2.1, §2.3 and §3.6 ("Hole").  Let `H` be a graph on a finite set of blocks `B` and
`S₀ ⊆ B` the hole.  A *hole polymer* is a connected block set `X ⊄ S₀` that contains each
connected component of `S₀` it meets (`HoleClosed`).  Its charged support is `X \\ S₀`, and two
hole polymers are incompatible iff their charged supports meet.  The size of a polymer is the
Steiner size `steiner H (X \\ S₀)`: the minimal cardinality of a connected set of blocks containing
`X \\ S₀`.

The block count `|X \\ S₀|` does not satisfy the entropy bound (many polymers have the same
charged part and a huge component of `S₀`), but the Steiner size does: a charged support `Y`
with Steiner size `n` through a block `b` is a subset of a lattice animal of `n` blocks through `b`
(`≤ Δ^{2(n-1)} 2^n` choices), and the polymers with charged support `Y` are determined by the
subset of the at most `Δ |Y|` hole blocks adjacent to `Y` that they contain (`≤ 2^{Δ|Y|}`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

variable {B : Type*} (H : SimpleGraph B) (S₀ : Finset B)

/-- `X` contains every connected component of the hole that it meets. -/
def HoleClosed (X : Finset B) : Prop :=
  ∀ a b, a ∈ S₀ → b ∈ S₀ → H.Adj a b → a ∈ X → b ∈ X

/-- Hole polymers: connected block sets not contained in the hole, containing or missing each
component of the hole. -/
abbrev HolePolymer := {X : Finset B // IsAnimal H X ∧ ¬ X ⊆ S₀ ∧ HoleClosed H S₀ X}

/-- The charged support of a hole polymer: its blocks outside the hole. -/
def holeSupp (X : HolePolymer H S₀) : Finset B := X.1 \ S₀

/-- The Steiner size of a set of blocks: the minimal cardinality of a connected set of blocks
containing it (the infimum over the empty set is `0`; it is never taken over the empty set for the
charged supports of hole polymers). -/
def steiner (Y : Finset B) : ℕ :=
  sInf {n | ∃ W : Finset B, IsAnimal H W ∧ Y ⊆ W ∧ W.card = n}

variable {H S₀}

theorem steiner_spec {Y : Finset B} (h : ∃ W : Finset B, IsAnimal H W ∧ Y ⊆ W) :
    ∃ W : Finset B, IsAnimal H W ∧ Y ⊆ W ∧ W.card = steiner H Y := by
  obtain ⟨W, hW, hYW⟩ := h
  exact Nat.sInf_mem (s := {n | ∃ W : Finset B, IsAnimal H W ∧ Y ⊆ W ∧ W.card = n})
    ⟨W.card, W, hW, hYW, rfl⟩

theorem steiner_le {Y W : Finset B} (hW : IsAnimal H W) (hYW : Y ⊆ W) :
    steiner H Y ≤ W.card :=
  Nat.sInf_le ⟨W, hW, hYW, rfl⟩

theorem card_le_steiner {Y : Finset B} (h : ∃ W : Finset B, IsAnimal H W ∧ Y ⊆ W) :
    Y.card ≤ steiner H Y := by
  obtain ⟨W, hW, hYW, hc⟩ := steiner_spec h
  rw [← hc]; exact Finset.card_le_card hYW

theorem exists_animal_of_holePolymer (X : HolePolymer H S₀) :
    ∃ W : Finset B, IsAnimal H W ∧ holeSupp H S₀ X ⊆ W :=
  ⟨X.1, X.2.1, Finset.sdiff_subset⟩

theorem holeSupp_nonempty (X : HolePolymer H S₀) : (holeSupp H S₀ X).Nonempty := by
  unfold holeSupp
  rw [Finset.sdiff_nonempty]
  exact X.2.2.1

/-- A union of connected sets, with overlaps along a connected graph, is connected. -/
theorem isAnimal_biUnion {n : ℕ} (W : Fin (n + 1) → Finset B) (hW : ∀ i, IsAnimal H (W i))
    (G : SimpleGraph (Fin (n + 1))) (hG : G.Connected)
    (hadj : ∀ i j, G.Adj i j → ¬ Disjoint (W i) (W j)) :
    IsAnimal H (Finset.univ.biUnion W) := by
  set U := Finset.univ.biUnion W with hU
  have hmem : ∀ i, ∀ p ∈ W i, p ∈ U := fun i p hp => by
    simp only [hU, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, hp⟩
  have hin : ∀ i, ∀ p ∈ W i, ∀ q ∈ W i,
      Relation.ReflTransGen (fun a b => a ∈ U ∧ b ∈ U ∧ H.Adj a b) p q := by
    intro i p hp q hq
    have := ((isAnimal_iff H _).mp (hW i)).2 p hp q hq
    exact Relation.ReflTransGen.mono (fun a b hab => ⟨hmem i a hab.1, hmem i b hab.2.1, hab.2.2⟩)
      _ _ this
  rw [isAnimal_iff]
  refine ⟨⟨((hW 0).1).choose, hmem 0 _ ((hW 0).1).choose_spec⟩, ?_⟩
  intro p hp q hq
  simp only [hU, Finset.mem_biUnion, Finset.mem_univ, true_and] at hp hq
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hq
  have hr := hG.preconnected i j
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  have key : ∀ k, Relation.ReflTransGen G.Adj i k →
      ∀ q ∈ W k, Relation.ReflTransGen (fun a b => a ∈ U ∧ b ∈ U ∧ H.Adj a b) p q := by
    intro k hk
    induction hk with
    | refl => intro q hq; exact hin i p hi q hq
    | @tail b c hab hbc ih =>
      intro q hq
      obtain ⟨r, hrb, hrc⟩ := Finset.not_disjoint_iff.mp (hadj b c hbc)
      exact (ih r hrb).trans (hin c r hrc q hq)
  exact key j hr q hj

/-- Subadditivity of the Steiner size along clusters with connected overlap graph. -/
theorem steiner_union_le {n : ℕ} (Y : Fin (n + 1) → Finset B)
    (hY : ∀ i, ∃ W : Finset B, IsAnimal H W ∧ Y i ⊆ W)
    (G : SimpleGraph (Fin (n + 1))) (hG : G.Connected)
    (hadj : ∀ i j, G.Adj i j → ¬ Disjoint (Y i) (Y j)) :
    steiner H (Finset.univ.biUnion Y) ≤ ∑ i, steiner H (Y i) := by
  choose W hW hYW hWc using fun i => steiner_spec (hY i)
  have hanimal := isAnimal_biUnion W hW G hG (fun i j hij hd => hadj i j hij
    (Finset.disjoint_of_subset_left (hYW i) (Finset.disjoint_of_subset_right (hYW j) hd)))
  calc steiner H (Finset.univ.biUnion Y) ≤ (Finset.univ.biUnion W).card :=
        steiner_le hanimal (Finset.biUnion_mono (fun i _ => hYW i))
    _ ≤ ∑ i, (W i).card := Finset.card_biUnion_le
    _ = ∑ i, steiner H (Y i) := Finset.sum_congr rfl (fun i _ => hWc i)

section Fibre

/-- A path inside `X` from a hole block to a block outside the hole leaves the hole at a block
`z ∈ X ∩ S₀` reachable inside the hole and adjacent to a block of `X \ S₀`. -/
theorem exit_exists {X : Finset B} (hX : IsAnimal H X) {v : B} (hv : v ∈ X) (hvS : v ∈ S₀)
    {y : B} (hy : y ∈ X) (hyS : y ∉ S₀) :
    ∃ z, z ∈ X ∧ z ∈ S₀ ∧
      Relation.ReflTransGen (fun a b => a ∈ S₀ ∧ b ∈ S₀ ∧ H.Adj a b) v z ∧
      ∃ y', y' ∈ X ∧ y' ∉ S₀ ∧ H.Adj z y' := by
  have hpath := ((isAnimal_iff H X).mp hX).2 v hv y hy
  have key : ∀ w, Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧ H.Adj a b) v w →
      (∃ z, z ∈ X ∧ z ∈ S₀ ∧
        Relation.ReflTransGen (fun a b => a ∈ S₀ ∧ b ∈ S₀ ∧ H.Adj a b) v z ∧
        ∃ y', y' ∈ X ∧ y' ∉ S₀ ∧ H.Adj z y') ∨
      (w ∈ S₀ ∧ w ∈ X ∧ Relation.ReflTransGen (fun a b => a ∈ S₀ ∧ b ∈ S₀ ∧ H.Adj a b) v w) := by
    intro w hw
    induction hw with
    | refl => exact Or.inr ⟨hvS, hv, Relation.ReflTransGen.refl⟩
    | @tail b c hab hbc ih =>
      rcases ih with ih | ⟨hbS, hbX, hbr⟩
      · exact Or.inl ih
      · by_cases hcS : c ∈ S₀
        · exact Or.inr ⟨hcS, hbc.2.1, hbr.tail ⟨hbS, hcS, hbc.2.2⟩⟩
        · exact Or.inl ⟨b, hbX, hbS, hbr, c, hbc.2.1, hcS, hbc.2.2⟩
  rcases key y hpath with h | ⟨hyS', -, -⟩
  · exact h
  · exact absurd hyS' hyS

theorem rtg_hole_symm {a b : B}
    (h : Relation.ReflTransGen (fun a b => a ∈ S₀ ∧ b ∈ S₀ ∧ H.Adj a b) a b) :
    Relation.ReflTransGen (fun a b => a ∈ S₀ ∧ b ∈ S₀ ∧ H.Adj a b) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail m c hab hbc ih =>
    exact (Relation.ReflTransGen.single ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩ :
      Relation.ReflTransGen (fun a b => a ∈ S₀ ∧ b ∈ S₀ ∧ H.Adj a b) c m).trans ih

/-- The hole blocks adjacent to a set `Y`. -/
def holeNbrs (Y : Finset B) : Finset B := S₀.filter (fun z => ∃ y ∈ Y, H.Adj z y)

theorem subset_of_inter_subset {X X' : HolePolymer H S₀}
    (hsupp : holeSupp H S₀ X = holeSupp H S₀ X')
    (hN : X.1 ∩ holeNbrs (H := H) (S₀ := S₀) (holeSupp H S₀ X) ⊆ X'.1) : X.1 ⊆ X'.1 := by
  intro v hv
  by_cases hvS : v ∈ S₀
  · obtain ⟨y, hy⟩ := holeSupp_nonempty X
    have hy' : y ∈ X.1 ∧ y ∉ S₀ := by simpa [holeSupp] using hy
    obtain ⟨z, hzX, hzS, hr, y', hy'X, hy'S, hadj⟩ :=
      exit_exists X.2.1 hv hvS hy'.1 hy'.2
    have hzN : z ∈ X.1 ∩ holeNbrs (H := H) (S₀ := S₀) (holeSupp H S₀ X) := by
      refine Finset.mem_inter.mpr ⟨hzX, ?_⟩
      unfold holeNbrs
      refine Finset.mem_filter.mpr ⟨hzS, y', ?_, hadj⟩
      simp [holeSupp, hy'X, hy'S]
    have hzX' := hN hzN
    -- the hole component of `z` lies in `X'`
    have hsymm : Relation.ReflTransGen (fun a b => a ∈ S₀ ∧ b ∈ S₀ ∧ H.Adj a b) z v :=
      rtg_hole_symm hr
    have key : ∀ w, Relation.ReflTransGen (fun a b => a ∈ S₀ ∧ b ∈ S₀ ∧ H.Adj a b) z w →
        w ∈ X'.1 := by
      intro w hw
      induction hw with
      | refl => exact hzX'
      | @tail b c hab hbc ih => exact X'.2.2.2 b c hbc.1 hbc.2.1 hbc.2.2 ih
    exact key v hsymm
  · have : v ∈ holeSupp H S₀ X := by simp [holeSupp, hv, hvS]
    rw [hsupp] at this
    exact (Finset.mem_sdiff.mp this).1

theorem holePolymer_ext {X X' : HolePolymer H S₀}
    (hsupp : holeSupp H S₀ X = holeSupp H S₀ X')
    (hN : X.1 ∩ holeNbrs (H := H) (S₀ := S₀) (holeSupp H S₀ X) =
      X'.1 ∩ holeNbrs (H := H) (S₀ := S₀) (holeSupp H S₀ X)) : X = X' := by
  apply Subtype.ext
  apply Finset.Subset.antisymm
  · exact subset_of_inter_subset hsupp (by rw [hN]; exact Finset.inter_subset_left)
  · refine subset_of_inter_subset hsupp.symm ?_
    rw [← hsupp, ← hN]
    exact Finset.inter_subset_left

variable [Fintype B] {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ)

include hdeg in
theorem card_holeNbrs_le (Y : Finset B) : (holeNbrs (H := H) (S₀ := S₀) Y).card ≤ Δ * Y.card := by
  have hsub : holeNbrs (H := H) (S₀ := S₀) Y ⊆ Y.biUnion (fun y => H.neighborFinset y) := by
    intro z hz
    unfold holeNbrs at hz
    obtain ⟨-, y, hy, hadj⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_biUnion.mpr ⟨y, hy, by simpa using hadj.symm⟩
  calc _ ≤ (Y.biUnion (fun y => H.neighborFinset y)).card := Finset.card_le_card hsub
    _ ≤ ∑ y ∈ Y, (H.neighborFinset y).card := Finset.card_biUnion_le
    _ ≤ ∑ y ∈ Y, Δ := Finset.sum_le_sum (fun y _ => by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg y)
    _ = Δ * Y.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

include hdeg in
/-- The polymers with a given charged support are determined by a subset of the hole blocks
adjacent to it. -/
theorem card_fibre_le (Y : Finset B) :
    ((Finset.univ : Finset (HolePolymer H S₀)).filter (fun X => holeSupp H S₀ X = Y)).card ≤
      2 ^ (Δ * Y.card) := by
  calc _ ≤ (Finset.powerset (holeNbrs (H := H) (S₀ := S₀) Y)).card := by
        refine Finset.card_le_card_of_injOn (fun X => X.1 ∩ holeNbrs (H := H) (S₀ := S₀) Y)
          (fun X _ => ?_) (fun X hX X' hX' h => ?_)
        · rw [Finset.mem_coe, Finset.mem_powerset]; exact Finset.inter_subset_right
        · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hX hX'
          refine holePolymer_ext (hX.trans hX'.symm) ?_
          rw [hX]; exact h
    _ = 2 ^ (holeNbrs (H := H) (S₀ := S₀) Y).card := Finset.card_powerset _
    _ ≤ 2 ^ (Δ * Y.card) := Nat.pow_le_pow_right (by norm_num) (card_holeNbrs_le hdeg Y)

end Fibre

section Entropy

variable [Fintype B] {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ)

include hdeg in
/-- The number of hole polymers through a block `b` of Steiner size `n + 1`. -/
theorem card_hole_class_le (b : B) (n : ℕ) :
    (((Finset.univ : Finset (HolePolymer H S₀)).filter (fun X => b ∈ holeSupp H S₀ X)).filter
      (fun X => steiner H (holeSupp H S₀ X) = n + 1)).card ≤
      Δ ^ (2 * n) * 2 ^ (n + 1) * 2 ^ (Δ * (n + 1)) := by
  set 𝒴 : Finset (Finset B) := (animals H b (n + 1)).biUnion (fun W => W.powerset) with h𝒴
  have hmaps : ∀ X ∈ ((Finset.univ : Finset (HolePolymer H S₀)).filter
      (fun X => b ∈ holeSupp H S₀ X)).filter (fun X => steiner H (holeSupp H S₀ X) = n + 1),
      holeSupp H S₀ X ∈ 𝒴 := by
    intro X hX
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
    obtain ⟨W, hW, hYW, hWc⟩ := steiner_spec (exists_animal_of_holePolymer X)
    rw [h𝒴, Finset.mem_biUnion]
    refine ⟨W, ?_, Finset.mem_powerset.mpr hYW⟩
    rw [mem_animals]
    exact ⟨hYW hX.1, by rw [hWc, hX.2], hW.2⟩
  have hY𝒴 : ∀ Y ∈ 𝒴, Y.card ≤ n + 1 := by
    intro Y hY
    rw [h𝒴, Finset.mem_biUnion] at hY
    obtain ⟨W, hW, hYW⟩ := hY
    rw [mem_animals] at hW
    rw [Finset.mem_powerset] at hYW
    exact hW.2.1 ▸ Finset.card_le_card hYW
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc _ ≤ ∑ Y ∈ 𝒴, 2 ^ (Δ * (n + 1)) := by
        refine Finset.sum_le_sum (fun Y hY => ?_)
        calc _ ≤ ((Finset.univ : Finset (HolePolymer H S₀)).filter
              (fun X => holeSupp H S₀ X = Y)).card := by
              refine Finset.card_le_card (fun X hX => ?_)
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX ⊢
              exact hX.2
          _ ≤ 2 ^ (Δ * Y.card) := card_fibre_le hdeg Y
          _ ≤ 2 ^ (Δ * (n + 1)) := Nat.pow_le_pow_right (by norm_num)
              (Nat.mul_le_mul_left _ (hY𝒴 Y hY))
    _ = 𝒴.card * 2 ^ (Δ * (n + 1)) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (Δ ^ (2 * n) * 2 ^ (n + 1)) * 2 ^ (Δ * (n + 1)) := by
        refine Nat.mul_le_mul_right _ ?_
        calc 𝒴.card ≤ ∑ W ∈ animals H b (n + 1), (W.powerset).card := Finset.card_biUnion_le
          _ = ∑ W ∈ animals H b (n + 1), 2 ^ (n + 1) := Finset.sum_congr rfl (fun W hW => by
              rw [Finset.card_powerset, (mem_animals H).mp hW |>.2.1])
          _ = (animals H b (n + 1)).card * 2 ^ (n + 1) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ Δ ^ (2 * n) * 2 ^ (n + 1) := by
              refine Nat.mul_le_mul_right _ ?_
              have := card_animals_le H hdeg b (n + 1)
              simpa using this
    _ = _ := by ring

include hdeg in
theorem sum_hole_le (b : B) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ X : HolePolymer H S₀, (if b ∈ holeSupp H S₀ X then f (steiner H (holeSupp H S₀ X)) else 0) ≤
      ∑ n ∈ range (Fintype.card B),
        ((Δ : ℝ) ^ (2 * n) * 2 ^ (n + 1) * 2 ^ (Δ * (n + 1))) * f (n + 1) := by
  have h1 : ∑ X : HolePolymer H S₀, (if b ∈ holeSupp H S₀ X then
      f (steiner H (holeSupp H S₀ X)) else 0) =
      ∑ X ∈ (Finset.univ : Finset (HolePolymer H S₀)).filter (fun X => b ∈ holeSupp H S₀ X),
        f (steiner H (holeSupp H S₀ X)) := by
    rw [Finset.sum_filter]
  rw [h1]
  have hpos : ∀ X : HolePolymer H S₀, b ∈ holeSupp H S₀ X → 1 ≤ steiner H (holeSupp H S₀ X) := by
    intro X hb
    have := card_le_steiner (exists_animal_of_holePolymer X)
    have h2 : 0 < (holeSupp H S₀ X).card := Finset.card_pos.mpr ⟨b, hb⟩
    omega
  have hmaps : ∀ X ∈ (Finset.univ : Finset (HolePolymer H S₀)).filter
      (fun X => b ∈ holeSupp H S₀ X), steiner H (holeSupp H S₀ X) - 1 ∈ range (Fintype.card B) := by
    intro X hX
    rw [Finset.mem_filter] at hX
    have h3 : steiner H (holeSupp H S₀ X) ≤ Fintype.card B :=
      (steiner_le X.2.1 Finset.sdiff_subset).trans (Finset.card_le_univ _)
    have h4 := hpos X hX.2
    have h5 : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨b⟩
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum (fun n hn => ?_)
  have hterm : ∀ X ∈ ((Finset.univ : Finset (HolePolymer H S₀)).filter
      (fun X => b ∈ holeSupp H S₀ X)).filter (fun X => steiner H (holeSupp H S₀ X) - 1 = n),
      f (steiner H (holeSupp H S₀ X)) = f (n + 1) := by
    intro X hX
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
    have h4 := hpos X hX.1
    congr 1; omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hcard : (((Finset.univ : Finset (HolePolymer H S₀)).filter
      (fun X => b ∈ holeSupp H S₀ X)).filter
      (fun X => steiner H (holeSupp H S₀ X) - 1 = n)).card ≤
      Δ ^ (2 * n) * 2 ^ (n + 1) * 2 ^ (Δ * (n + 1)) := by
    refine le_trans (le_of_eq ?_) (card_hole_class_le (S₀ := S₀) hdeg b n)
    congr 1
    ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hb, h⟩; exact ⟨hb, by have := hpos X hb; omega⟩
    · rintro ⟨hb, h⟩; exact ⟨hb, by omega⟩
  calc _ ≤ ((Δ ^ (2 * n) * 2 ^ (n + 1) * 2 ^ (Δ * (n + 1)) : ℕ) : ℝ) * f (n + 1) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hf _)
    _ = _ := by push_cast; ring

section Expansion

variable {ε κ κ' α : ℝ}

include hdeg in
/-- The entropy sum over hole polymers through a block, in the Steiner size. -/
theorem entropy_hole (hε : 0 ≤ ε)
    (hq : (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α)) < 1)
    (hcond : ε * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α)) /
      (1 - (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α))) ≤ α) (b : B) :
    ∑ X : HolePolymer H S₀, (if b ∈ holeSupp H S₀ X then
      ε * Real.exp ((κ' + α - κ) * (steiner H (holeSupp H S₀ X) : ℝ)) else 0) ≤ α := by
  set q : ℝ := (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α)) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have h1 := sum_hole_le (S₀ := S₀) hdeg b (fun n => ε * Real.exp ((κ' + α - κ) * (n : ℝ)))
    (fun n => by positivity)
  refine h1.trans ?_
  have h2 : ∀ n ∈ range (Fintype.card B), ((Δ : ℝ) ^ (2 * n) * 2 ^ (n + 1) * 2 ^ (Δ * (n + 1))) *
      (ε * Real.exp ((κ' + α - κ) * ((n + 1 : ℕ) : ℝ))) =
      ε * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α)) * q ^ n := by
    intro n _
    have eexp : Real.exp ((κ' + α - κ) * ((n + 1 : ℕ) : ℝ)) =
        Real.exp (-(κ - κ' - α)) * Real.exp (-(κ - κ' - α)) ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    have e2 : (2 : ℝ) ^ (n + 1) * 2 ^ (Δ * (n + 1)) = 2 ^ (Δ + 1) * (2 ^ (Δ + 1)) ^ n := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring
    have e3 : (Δ : ℝ) ^ (2 * n) = ((Δ : ℝ) ^ 2) ^ n := pow_mul _ _ _
    calc _ = ((Δ : ℝ) ^ 2) ^ n * ((2 : ℝ) ^ (n + 1) * 2 ^ (Δ * (n + 1))) *
          (ε * (Real.exp (-(κ - κ' - α)) * Real.exp (-(κ - κ' - α)) ^ n)) := by
          rw [e3, eexp]; ring
      _ = _ := by rw [e2, hqdef, mul_pow, mul_pow]; ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  have h3 : ∑ i ∈ range (Fintype.card B), q ^ i ≤ (1 - q)⁻¹ :=
    sum_le_hasSum _ (fun i _ => by positivity) (hasSum_geometric_of_lt_one hq0 hq)
  calc ε * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α)) * ∑ i ∈ range (Fintype.card B), q ^ i
      ≤ ε * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α)) * (1 - q)⁻¹ :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ε * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α)) / (1 - q) := by rw [div_eq_mul_inv]
    _ ≤ α := hcond

include hdeg in
/-- The polymer expansion with a hole, with decay in the Steiner size.  The activities of the hole
polymers `X` (connected, not inside the hole, containing or missing each component of the hole) are
bounded by `ε e^{-κ · steiner(X \ S₀)}`; incompatibility is overlap outside the hole.  The local
terms are indexed by sets `Y` of blocks (charged supports) and decay like `e^{-κ' · steiner Y}`. -/
theorem pe_hole (hε : 0 ≤ ε) (hκ' : 0 ≤ κ')
    (hq : (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α)) < 1)
    (hcond : ε * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α)) /
      (1 - (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α))) ≤ α)
    (K : HolePolymer H S₀ → ℂ)
    (hK : ∀ X, ‖K X‖ ≤ ε * Real.exp (-κ * (steiner H (holeSupp H S₀ X) : ℝ))) :
    Xi (shareBlock (holeSupp H S₀)) K = Complex.exp (logSeries (shareBlock (holeSupp H S₀)) K) ∧
    logSeries (shareBlock (holeSupp H S₀)) K =
      ∑ Y : Finset B, PY (shareBlock (holeSupp H S₀)) (holeSupp H S₀) K Y ∧
    (∀ b : B, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY (shareBlock (holeSupp H S₀)) (holeSupp H S₀) K Y‖ *
          Real.exp (κ' * (steiner H Y : ℝ)) ≤ α) ∧
    ‖logSeries (shareBlock (holeSupp H S₀)) K‖ ≤ ((Finset.univ \ S₀).card : ℝ) * α ∧
    Real.exp (-(((Finset.univ \ S₀).card : ℝ) * α)) ≤ ‖Xi (shareBlock (holeSupp H S₀)) K‖ ∧
    ‖Xi (shareBlock (holeSupp H S₀)) K‖ ≤ Real.exp (((Finset.univ \ S₀).card : ℝ) * α) := by
  have hα : 0 ≤ α := by
    refine le_trans ?_ hcond
    have : 0 < 1 - (Δ : ℝ) ^ 2 * 2 ^ (Δ + 1) * Real.exp (-(κ - κ' - α)) := by linarith
    positivity
  have hent := entropy_hole (S₀ := S₀) hdeg hε hq hcond
  refine pe_sized (holeSupp H S₀) (fun X => (steiner H (holeSupp H S₀ X) : ℝ))
    (fun Y => κ' * (steiner H Y : ℝ)) hε hα holeSupp_nonempty
    (fun X => by exact_mod_cast card_le_steiner (exists_animal_of_holePolymer X))
    (fun Y => by positivity) (fun X => le_rfl) ?_ hent (Finset.univ \ S₀) ?_ K hK
  · intro n X hconn
    have hsum := steiner_union_le (H := H) (fun i => holeSupp H S₀ (X i))
      (fun i => exists_animal_of_holePolymer (X i)) (clusterGraph (shareBlock (holeSupp H S₀)) X)
      hconn (fun i j hij => (lnk_shareBlock _ _ _).mp (clusterGraph_adj _ _ i j |>.mp hij).2)
    calc κ' * (steiner H (unionOf (holeSupp H S₀) X) : ℝ)
        ≤ κ' * ((∑ i, steiner H (holeSupp H S₀ (X i)) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hsum) hκ'
      _ = ∑ i, κ' * (steiner H (holeSupp H S₀ (X i)) : ℝ) := by
          push_cast; rw [Finset.mul_sum]
      _ ≤ _ := by simp
  · intro X
    obtain ⟨b, hb⟩ := holeSupp_nonempty X
    refine ⟨b, ?_, hb⟩
    have := (Finset.mem_sdiff.mp hb).2
    simp [this]

end Expansion

end Entropy

end Balaban.Polymer
