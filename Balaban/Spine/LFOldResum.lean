/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldBBound
public import Balaban.Fluctuation.LocalPairLevelInner
public import Balaban.Fluctuation.LocalPairDepth

/-!
# The resummation over the decoupling families at a mark site (P3 (4.45)–(4.49); P6 p. 34)

This file proves the named input `OldResumSite`.

* `subset_cubeIdx_locG'`: **the cubes of a family are cubes of the cover of its local pair** when the
  collar `r'` of the local set is at least the side `L^{k+1+m₁}` of the cells of the top layer (the
  layers of `G′ ∩ 𝔹_{k+1}(V)` are those of `G′` on the cells inside `V`); hence `|J_V| = |J|`
  (`card_locCubes_eq`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

/-- **The union of the `π'_j`-cubes based at the cells of the sites of a set** `B`. -/
def boxUnion (m₀ j : ℕ) (B : Set (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  {x | ∃ y ∈ B, x ∈ box (cbase (cellSide L m₀ m₁ j) y) (L * cellSide L m₀ m₁ j)}

open Classical in
/-- **The size of a connected union of `π'_j`-cubes by the number of its base cells** (P3 (4.48)):
if the union `V` of the `π'_j`-cubes based at the cells of the sites of `B` is a set of `𝒟_j`, then
`d^cov_j(V) ≤ (4 d L + 1 + 2 d L^{d+1}) · #cells(B)`.  The base cells, joined along the nearest-
neighbour connectivity of `V` at the cost `4 d L + 1` per pair of touching cubes (`assemble`), are
met by a connected structure; every `π'_j`-cube in `V` is then attached at the cost `2 d L`
(`extend_tree_of_linked`), and `V` has at most `L^d · #cells(B)` cells. -/
theorem treeLenCovOne_boxUnion_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (B : Set (CTorus d L N₁ m₁ K))
    (hV : IsDj m₀ j (boxUnion m₀ j B)) :
    treeLenCovOne m₀ j (boxUnion m₀ j B) ≤
      (4 * d * L + 1 + 2 * d * L * (L : ℝ) ^ d) *
        ((B.toFinset.image (cbase (cellSide L m₀ m₁ j))).card : ℝ) := by
  classical
  set a := cellSide L m₀ m₁ j with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ j
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLa : 0 < L * a := Nat.mul_pos hL0 ha0
  set V := boxUnion m₀ j B with hVdef
  set C := B.toFinset.image (cbase a) with hC
  set ω : CTorus d L N₁ m₁ K → CTorus d L N₁ m₁ K → ℝ := scaleW L m₀ m₁ j with hωdef
  have haR : ((a : ℕ) : ℝ) = (L : ℝ) ^ (m₀ + m₁ + j) := by
    rw [ha]; unfold cellSide; push_cast; congr 1; ring
  have haRpos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hω0 : ∀ x y, 0 ≤ ω x y := fun x y => by simp only [hωdef, scaleW]; positivity
  have hωa : ∀ x y, ω x y = ((a : ℕ) : ℝ)⁻¹ := fun x y => by simp only [hωdef, scaleW, haR]
  have hωc : ∀ x ∈ V, ∀ y ∈ V, ω x y ≤ ((a : ℕ) : ℝ)⁻¹ := fun x _ y _ => le_of_eq (hωa x y)
  have hainv : ((a : ℕ) : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ haRpos]; exact_mod_cast ha0
  have hpair : 2 * ((d : ℝ) * ((L * a : ℕ) : ℝ) * ((a : ℕ) : ℝ)⁻¹) = 2 * d * L := by
    push_cast; field_simp
  -- the cubes of the base cells lie in `V`
  have hmemC : ∀ c ∈ C, ∃ y ∈ B, c = cbase a y := fun c hc => by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨y, Set.mem_toFinset.1 hy, rfl⟩
  have hboxV : ∀ c ∈ C, box c (L * a) ⊆ V := fun c hc => by
    obtain ⟨y, hy, rfl⟩ := hmemC c hc
    exact fun x hx => ⟨y, hy, hx⟩
  have hcbox : ∀ c : CTorus d L N₁ m₁ K, c ∈ box c (L * a) := fun c => mem_box_self c hLa
  have hnode : ∀ x ∈ V, ∃ c ∈ C, x ∈ box c (L * a) := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨cbase a y, Finset.mem_image_of_mem _ (Set.mem_toFinset.2 hy), hxy⟩
  have hlinkbox : ∀ c ∈ C, ∀ x ∈ box c (L * a), ∀ y ∈ box c (L * a),
      Linked V ω (2 * d * L) x y := fun c hc x hx y hy => by
    have := linked_box_pair hω0 c (L * a) (hboxV c hc) hωc hx hy
    rwa [hpair] at this
  -- the nerve of the base cells
  set H : CTorus d L N₁ m₁ K → CTorus d L N₁ m₁ K → Prop := fun u v =>
    ∃ x ∈ box u (L * a), ∃ y ∈ box v (L * a), x = y ∨ Nbr x y with hHdef
  have hlink : ∀ u ∈ C, ∀ v ∈ C, H u v → ∃ x ∈ ({u} : Finset _), ∃ y ∈ ({v} : Finset _),
      Linked V ω (4 * d * L + 1) x y := by
    intro u hu v hv ⟨x, hx, y, hy, hxy⟩
    refine ⟨u, Finset.mem_singleton_self u, v, Finset.mem_singleton_self v, ?_⟩
    have h1 := hlinkbox u hu u (hcbox u) x hx
    have h3 := hlinkbox v hv y hy v (hcbox v)
    have hxV : x ∈ V := hboxV u hu hx
    have hyV : y ∈ V := hboxV v hv hy
    have h2 : Linked V ω ((a : ℕ) : ℝ)⁻¹ x y := by
      rcases hxy with rfl | hn
      · exact Linked.refl (inv_nonneg.2 haRpos.le) hxV
      · exact Linked.step hn hxV hyV (le_of_eq (hωa x y))
    refine ((h1.trans hω0 h2).trans hω0 h3).mono_c ?_
    linarith
  -- the nerve is connected
  obtain ⟨x₀, hx₀⟩ := hV.1
  obtain ⟨v₀, hv₀, hx₀v₀⟩ := hnode x₀ hx₀
  have hreach : ∀ v ∈ C, Relation.ReflTransGen (fun u v => H u v ∧ u ∈ C ∧ v ∈ C) v₀ v := by
    intro v hv
    have key : ∀ x, Relation.ReflTransGen (fun u v => u ∈ V ∧ v ∈ V ∧ Nbr u v) x₀ x →
        ∃ c ∈ C, x ∈ box c (L * a) ∧
          Relation.ReflTransGen (fun u v => H u v ∧ u ∈ C ∧ v ∈ C) v₀ c := by
      intro x hx
      induction hx with
      | refl => exact ⟨v₀, hv₀, hx₀v₀, Relation.ReflTransGen.refl⟩
      | @tail b c' _ hbc ih =>
        obtain ⟨cb, hcb, hbcb, hpath⟩ := ih
        obtain ⟨cc, hcc, hccb⟩ := hnode c' hbc.2.1
        exact ⟨cc, hcc, hccb, hpath.tail ⟨⟨b, hbcb, c', hccb, Or.inr hbc.2.2⟩, hcb, hcc⟩⟩
    obtain ⟨c, hc, hvc, hpath⟩ := key v (hV.2.2 x₀ hx₀ v (hboxV v hv (hcbox v)))
    exact hpath.tail ⟨⟨v, hvc, v, hcbox v, Or.inl rfl⟩, hc, hv⟩
  have hcov := assemble hω0 C H v₀ hv₀ hreach (fun v => {v}) (fun _ => 0)
    (fun v hv => ⟨{v}, ∅, connStruct_singleton v, by simpa using hboxV v hv (hcbox v), subset_rfl,
      by simp [bondCost]⟩) (4 * d * L + 1) hlink
  obtain ⟨W, E, hcW, hWV, hCW, hcost⟩ := hcov
  have hCW' : ∀ c ∈ C, c ∈ W := fun c hc => hCW (Finset.mem_biUnion.2 ⟨c, hc, by simp⟩)
  obtain ⟨W', E', g1, g2, g3, g4⟩ := extend_tree_of_linked (m₀ := m₀) (j := j) hω0 hcW hWV
    (by positivity : (0 : ℝ) ≤ 2 * d * L) fun b hb => by
      obtain ⟨c, hc, hbc⟩ := hnode b (hb.2 (mem_box_self b hLa))
      exact ⟨c, hCW' c hc, hlinkbox c hc c (hcbox c) b hbc⟩
  have hcells : (cellCount a V : ℝ) ≤ (L : ℝ) ^ d * C.card := by
    have h1 : (Finset.univ.filter fun b : CTorus d L N₁ m₁ K => Aligned a b ∧ box b a ⊆ V) ⊆
        C.biUnion fun c => Finset.univ.filter fun b : CTorus d L N₁ m₁ K =>
          Aligned a b ∧ b ∈ box c (L * a) := by
      intro b hb
      obtain ⟨hal, hbV⟩ := (Finset.mem_filter.1 hb).2
      obtain ⟨c, hc, hbc⟩ := hnode b (hbV (mem_box_self b ha0))
      exact Finset.mem_biUnion.2 ⟨c, hc, Finset.mem_filter.2 ⟨Finset.mem_univ _, hal, hbc⟩⟩
    have h2 : (cellCount a V) ≤ C.card * L ^ d := by
      unfold cellCount
      refine (Finset.card_le_card h1).trans (Finset.card_biUnion_le.trans ?_)
      calc ∑ c ∈ C, (Finset.univ.filter fun b : CTorus d L N₁ m₁ K =>
            Aligned a b ∧ b ∈ box c (L * a)).card ≤ ∑ _c ∈ C, L ^ d :=
            Finset.sum_le_sum fun c hc => by
              obtain ⟨y, -, rfl⟩ := hmemC c hc
              exact card_aligned_in_cube hdvd ha0 (aligned_cbase y)
        _ = C.card * L ^ d := by rw [Finset.sum_const, smul_eq_mul]
    calc (cellCount a V : ℝ) ≤ ((C.card * L ^ d : ℕ) : ℝ) := by exact_mod_cast h2
      _ = (L : ℝ) ^ d * C.card := by push_cast; ring
  have hCpos : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
  calc treeLenCovOne m₀ j V ≤ bondCost ω E' := treeLenCovOne_le_of_chosen (fullCover_chosen hV) g1 g2 g3
    _ ≤ bondCost ω E + (cellCount a V : ℝ) * (2 * d * L) := g4
    _ ≤ (∑ _v ∈ C, (0 : ℝ) + ((C.card : ℝ) - 1) * (4 * d * L + 1)) +
          (L : ℝ) ^ d * C.card * (2 * d * L) :=
        add_le_add hcost (mul_le_mul_of_nonneg_right hcells (by positivity))
    _ ≤ _ := by
        rw [Finset.sum_const_zero, zero_add]
        nlinarith [mul_nonneg hCpos (by positivity : (0 : ℝ) ≤ 4 * d * L + 1)]

end Balaban.Fluctuation

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background
  Balaban.Polymer

namespace Balaban.RootFSpine

section Resum

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

omit [NeZero M] in
/-- **The cubes of a family are cubes of the cover of its local pair** (reading HS-1′): if the collar
`r'` of the local set `V(X, J)` is at least `L^{k+1+m₁}`, every cube `(j, y)` of a family `J` of
cubes of the cover of `G′` is a cube of the cover of `G′ ∩ 𝔹_{k+1}(V(X, J))`: the cell of side
`L^{k+1+m₁}` of its base lies in `V(X, J)`, so the base is in the top layer of `𝔹_{k+1}(V(X, J))`
and the layers of the two sets agree there. -/
theorem subset_cubeIdx_locG' (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) {ρ r r' : ℕ} (hr' : S.L ^ (k + 1 + m₁) ≤ r')
    (X : Finset (Torus S.d (n k))) {J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (hJ : J ∈ allJ g hnn hM1 H hk hρ ρ) :
    J ⊆ (coverOf (locG' g hnn hM1 H hk hρ (locSetXJ g hM1 H r r' X J))).cubeIdx := by
  classical
  intro P hP
  have hPg : P ∈ (coverOf (stepG' g hnn hM1 H hk hρ)).cubeIdx :=
    (Finset.mem_filter.1 (Finset.mem_powerset.1 hJ hP)).1
  obtain ⟨hj, hlay, hbase⟩ := (mem_cubeIdx _).1 hPg
  refine (mem_cubeIdx _).2 ⟨hj, ?_, hbase⟩
  obtain ⟨hyΩ, hyΩ'⟩ := (GeneratingSet.mem_layer _).1 hlay
  have htop : P.2 ∈ (locB g hM1 (locSetXJ g hM1 H r r' X J)).Ω (k + 1) := by
    refine (mem_localB_Ω_top_sameCell le_rfl _ (minSep_le_locB g hM1) P.2).2 fun w hw => ?_
    refine ⟨P.2, Or.inr ⟨P, hP, (mem_cubeP).2 (SameCell.refl _ _)⟩, ?_⟩
    exact (supDist_le_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _) hw).trans hr'
  have hB : P.2 ∈ (locB g hM1 (locSetXJ g hM1 H r r' X J)).Ω P.1 :=
    GeneratingSet.Ω_antitone (locB g hM1 (locSetXJ g hM1 H r r' X J)) hj.1 hj.2 (Nat.le_succ _) htop
  refine (GeneratingSet.mem_layer _).2 ⟨?_, fun h => hyΩ' ?_⟩
  · show P.2 ∈ (stepG' g hnn hM1 H hk hρ).Ω P.1 ∩ (locB g hM1 (locSetXJ g hM1 H r r' X J)).Ω P.1
    exact Finset.mem_inter.2 ⟨hyΩ, hB⟩
  · have h' : P.2 ∈ (stepG' g hnn hM1 H hk hρ).Ω (P.1 + 1) ∩
        (locB g hM1 (locSetXJ g hM1 H r r' X J)).Ω (P.1 + 1) := h
    exact (Finset.mem_inter.1 h').1

omit [NeZero M] in
/-- **`|J_V| = |J|`** for the families of the old part (`subset_cubeIdx_locG'`). -/
theorem card_locCubes_eq (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) {ρ r r' : ℕ} (hr' : S.L ^ (k + 1 + m₁) ≤ r')
    (X : Finset (Torus S.d (n k))) {J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (hJ : J ∈ allJ g hnn hM1 H hk hρ ρ) :
    (locCubes g (coverOf (locG' g hnn hM1 H hk hρ (locSetXJ g hM1 H r r' X J))) J).card = J.card := by
  classical
  have hsub := subset_cubeIdx_locG' g hnn hM1 H hk hρ (r := r) hr' X hJ
  unfold locCubes
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext P
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact hQ
  · intro hP
    exact ⟨⟨P, hsub hP⟩, hP, rfl⟩

end Resum

end Balaban.RootFSpine
