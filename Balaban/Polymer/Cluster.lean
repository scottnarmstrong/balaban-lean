module

public import Balaban.Polymer.Ursell

/-!
# Clusters of polymers

For a relation `inc` on a type `P` of polymers, a cluster is a tuple `X : ι → P`; its
incompatibility graph has the pairs of distinct positions whose polymers are incompatible.
`clusterUrsell` is the Ursell function of the cluster on the full position set.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer

variable {P : Type*} (inc : P → P → Prop)

/-- Symmetrized incompatibility. -/
def lnk (x y : P) : Prop := inc x y ∨ inc y x

theorem lnk_symm (x y : P) : lnk inc x y ↔ lnk inc y x := or_comm

/-- The incompatibility graph of a cluster `X`. -/
def clusterGraph {ι : Type*} (X : ι → P) : SimpleGraph ι :=
  SimpleGraph.fromRel (fun i j => inc (X i) (X j))

theorem clusterGraph_adj {ι : Type*} (X : ι → P) (i j : ι) :
    (clusterGraph inc X).Adj i j ↔ i ≠ j ∧ lnk inc (X i) (X j) := Iff.rfl

/-- The Ursell function of a cluster. -/
def clusterUrsell {ι : Type*} (X : ι → P) (S : Finset ι) : ℤ := ursell (clusterGraph inc X) S

/-- The sign of the Ursell function: `(-1)^(|S|-1) φ(S) ≥ 0` for nonempty `S`. -/
theorem ursell_sign {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) :
    ∀ (n : ℕ) (S : Finset ι), S.card = n + 1 → 0 ≤ (-1 : ℤ) ^ n * ursell G S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS
    obtain ⟨v, hv⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    set U := S.erase v with hU
    have hvU : v ∉ U := Finset.notMem_erase v S
    have hSU : insert v U = S := Finset.insert_erase hv
    have hUc : U.card = n := by
      rw [hU, Finset.card_erase_of_mem hv]; omega
    rw [← hSU]
    rcases U.eq_empty_or_nonempty with hUe | ⟨u0, hu0⟩
    · rw [hUe]
      have : n = 0 := by rw [← hUc, hUe]; rfl
      subst this
      simp [ursell_singleton]
    · rw [ursell_insert_rec G hvU hu0, Finset.mul_sum]
      refine Finset.sum_nonneg (fun T hT => ?_)
      rw [Finset.mem_filter, Finset.mem_powerset] at hT
      obtain ⟨hTU, hu0T⟩ := hT
      have hTc : 1 ≤ T.card := Finset.card_pos.mpr ⟨u0, hu0T⟩
      have hTc' : T.card ≤ n := hUc ▸ Finset.card_le_card hTU
      have hRc : (U \ T).card = n - T.card := by
        rw [Finset.card_sdiff_of_subset hTU, hUc]
      -- IH for `T` and `insert v (U \ T)`
      obtain ⟨t, ht⟩ : ∃ t, T.card = t + 1 := ⟨T.card - 1, by omega⟩
      have hT0 := ih t (by omega) T ht
      have hR0 := ih (n - T.card) (by omega) (insert v (U \ T)) (by
        rw [Finset.card_insert_of_notMem (fun h => hvU (Finset.sdiff_subset h)), hRc])
      have hsign : (-1 : ℤ) ^ n = (-1) ^ (t + 1) * (-1) ^ (n - T.card) := by
        rw [← pow_add]; congr 1; omega
      have : (-1 : ℤ) ^ n * ((-(if (T.filter (G.Adj v)).Nonempty then 1 else 0 : ℤ)) * ursell G T *
          ursell G (insert v (U \ T))) =
          (if (T.filter (G.Adj v)).Nonempty then 1 else 0 : ℤ) *
            (-((-1) ^ (t + 1) * ursell G T)) * ((-1) ^ (n - T.card) * ursell G (insert v (U \ T))) := by
        rw [hsign]; ring
      rw [this]
      have h1 : 0 ≤ (if (T.filter (G.Adj v)).Nonempty then 1 else 0 : ℤ) := by split_ifs <;> norm_num
      have h2 : -((-1 : ℤ) ^ (t + 1) * ursell G T) = (-1) ^ t * ursell G T := by
        rw [pow_succ]; ring
      rw [h2]
      exact mul_nonneg (mul_nonneg h1 hT0) hR0

theorem clusterGraph_comap {ι ι' : Type*} (f : ι' ↪ ι) (X : ι → P) :
    (clusterGraph inc X).comap f = clusterGraph inc (X ∘ f) := by
  ext i j
  simp only [SimpleGraph.comap_adj, clusterGraph_adj, Function.comp_apply]
  rw [f.injective.ne_iff]

theorem clusterUrsell_comap {ι ι' : Type*} [DecidableEq ι] (f : ι' ↪ ι) (X : ι → P)
    (S' : Finset ι') :
    clusterUrsell inc (X ∘ f) S' = clusterUrsell inc X (S'.map f) := by
  unfold clusterUrsell
  rw [← clusterGraph_comap, ursell_comap]

theorem clusterUrsell_congr {ι : Type*} {X X' : ι → P} {S : Finset ι}
    (h : ∀ i ∈ S, X i = X' i) : clusterUrsell inc X S = clusterUrsell inc X' S := by
  unfold clusterUrsell
  refine ursell_congr (fun x hx y hy => ?_)
  rw [clusterGraph_adj, clusterGraph_adj, h x hx, h y hy]

/-! ### Tuples frozen outside a set -/

section Fn

variable [Fintype P] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The tuples that equal `b` outside `R`. -/
def Fn (b : ι → P) (R : Finset ι) : Finset (ι → P) :=
  Fintype.piFinset (fun i => if i ∈ R then Finset.univ else {b i})

theorem mem_Fn {b : ι → P} {R : Finset ι} {X : ι → P} : X ∈ Fn b R ↔ ∀ i, i ∉ R → X i = b i := by
  simp only [Fn, Fintype.mem_piFinset]
  refine forall_congr' (fun i => ?_)
  by_cases hi : i ∈ R <;> simp [hi]

theorem Fn_empty (b : ι → P) : Fn b ∅ = {b} := by
  ext X
  rw [mem_Fn, Finset.mem_singleton]
  simp only [Finset.notMem_empty, not_false_eq_true, forall_const]
  exact ⟨fun h => funext h, fun h i => by rw [h]⟩

/-- Merge two tuples along a set. -/
def merge (T : Finset ι) (X X' : ι → P) : ι → P := fun i => if i ∈ T then X i else X' i

theorem sum_Fn_union {A : Type*} [AddCommMonoid A] (b : ι → P) {T R : Finset ι}
    (hdisj : Disjoint T R) (f : (ι → P) → A) :
    ∑ X ∈ Fn b (T ∪ R), f X = ∑ X ∈ Fn b T, ∑ X' ∈ Fn b R, f (merge T X X') := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p => merge T p.1 p.2)
    (fun X => (fun i => if i ∈ T then X i else b i, fun i => if i ∈ R then X i else b i))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨X, X'⟩ hp
    rw [Finset.mem_product, mem_Fn, mem_Fn] at hp
    obtain ⟨hp1, hp2⟩ := hp
    dsimp only at hp1 hp2
    rw [mem_Fn]
    intro i hi
    rw [Finset.mem_union, not_or] at hi
    simp [merge, hi.1, hp2 i hi.2]
  · intro X hX
    rw [mem_Fn] at hX
    rw [Finset.mem_product, mem_Fn, mem_Fn]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · simp [hi]
    · simp [hi]
  · rintro ⟨X, X'⟩ hp
    rw [Finset.mem_product, mem_Fn, mem_Fn] at hp
    obtain ⟨hp1, hp2⟩ := hp
    dsimp only at hp1 hp2
    ext i
    · by_cases hi : i ∈ T
      · simp [merge, hi]
      · simp [hi, hp1 i hi]
    · by_cases hi : i ∈ R
      · have : i ∉ T := Finset.disjoint_right.mp hdisj hi
        simp [merge, hi, this]
      · simp [hi, hp2 i hi]
  · intro X hX
    rw [mem_Fn] at hX
    ext i
    by_cases hi : i ∈ T
    · simp [merge, hi]
    · by_cases hiR : i ∈ R
      · simp [merge, hi, hiR]
      · have := hX i (by rw [Finset.mem_union, not_or]; exact ⟨hi, hiR⟩)
        simp [merge, hi, hiR, this]
  · intro p _
    rfl

end Fn

section Rooted

variable [Fintype P] {A : Type*} [CommRing A]

/-- The block sums `c_m` of the recursion. -/
def blkc (Y : P) (K : P → A) (m : ℕ) : A :=
  ∑ X : Fin m → P, (if ∃ i, lnk inc Y (X i) then (1 : A) else 0) *
    (clusterUrsell inc X Finset.univ : A) * ∏ i, K (X i)

/-- The solution of the block recursion. -/
def ZZ (c : ℕ → A) : ℕ → A
  | 0 => 1
  | n + 1 => -∑ m : Fin (n + 1), ((n.choose m : ℕ) : A) * c (m + 1) * ZZ c (n - m)
termination_by n => n
decreasing_by omega

theorem ZZ_zero (c : ℕ → A) : ZZ c 0 = 1 := by rw [ZZ]

theorem ZZ_succ (c : ℕ → A) (n : ℕ) :
    ZZ c (n + 1) = -∑ m ∈ Finset.range (n + 1), ((n.choose m : ℕ) : A) * c (m + 1) * ZZ c (n - m) := by
  rw [ZZ, Fin.sum_univ_eq_sum_range (fun m => ((n.choose m : ℕ) : A) * c (m + 1) * ZZ c (n - m))]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem blk_eq (Y : P) (K : P → A) (T : Finset ι) :
    ∑ X ∈ Fn (fun _ => Y) T, (if ∃ i ∈ T, lnk inc Y (X i) then (1 : A) else 0) *
      (clusterUrsell inc X T : A) * ∏ i ∈ T, K (X i) = blkc inc Y K T.card := by
  let e : Fin T.card ≃ T := T.equivFin.symm
  let f : Fin T.card ↪ ι := ⟨fun k => (e k).1, fun a b h => e.injective (Subtype.ext h)⟩
  have hfe : ∀ k, f k = (e k).1 := fun _ => rfl
  have hfs : ∀ (j : ι) (hj : j ∈ T), f (e.symm ⟨j, hj⟩) = j := by
    intro j hj; rw [hfe]; simp
  have hfk : ∀ (k : Fin T.card) (hk : f k ∈ T), e.symm ⟨f k, hk⟩ = k := by
    intro k hk
    have : (⟨f k, hk⟩ : T) = e k := Subtype.ext rfl
    rw [this, e.symm_apply_apply]
  have hT : (Finset.univ : Finset (Fin T.card)).map f = T := by
    ext j
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩; exact (e k).2
    · intro hj; exact ⟨e.symm ⟨j, hj⟩, hfs j hj⟩
  rw [blkc]
  refine Finset.sum_nbij' (fun X => X ∘ f)
    (fun X' => fun j => if h : j ∈ T then X' (e.symm ⟨j, h⟩) else Y) ?_ ?_ ?_ ?_ ?_
  · intro X _; exact Finset.mem_univ _
  · intro X' _
    rw [mem_Fn]
    intro j hj
    simp [hj]
  · intro X hX
    rw [mem_Fn] at hX
    ext j
    by_cases hj : j ∈ T
    · simp only [hj, dite_true, Function.comp_apply, hfs j hj]
    · simp [hj, hX j hj]
  · intro X' _
    ext k
    have hk : f k ∈ T := (e k).2
    simp only [Function.comp_apply, hk, dite_true, hfk k hk]
  · intro X _
    have h1 : clusterUrsell inc (X ∘ f) Finset.univ = clusterUrsell inc X T := by
      rw [clusterUrsell_comap, hT]
    have h2 : (∃ i ∈ T, lnk inc Y (X i)) ↔ ∃ k, lnk inc Y ((X ∘ f) k) := by
      constructor
      · rintro ⟨i, hi, h⟩
        rw [← hT] at hi
        obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hi
        exact ⟨k, h⟩
      · rintro ⟨k, h⟩
        exact ⟨f k, (e k).2, h⟩
    have h3 : ∏ i ∈ T, K (X i) = ∏ k, K ((X ∘ f) k) := by
      calc ∏ i ∈ T, K (X i) = ∏ i ∈ Finset.map f Finset.univ, K (X i) := by rw [hT]
        _ = _ := by rw [Finset.prod_map]; rfl
    rw [h1, h3]
    simp only [h2]

end Rooted

section RootedSum

variable [Fintype P] {A : Type*} [CommRing A] {N : ℕ}

/-- The rooted cluster sum over the positions `R` (the root is the position `0`). -/
def Zr (Y : P) (K : P → A) (R : Finset (Fin (N + 1))) : A :=
  ∑ X ∈ Fn (fun _ => Y) R, (clusterUrsell inc X (insert 0 R) : A) * ∏ i ∈ R, K (X i)

theorem adj_root {Y : P} {R T : Finset (Fin (N + 1))} (h0 : (0 : Fin (N + 1)) ∉ R) (hT : T ⊆ R)
    {X : Fin (N + 1) → P} (hX : X ∈ Fn (fun _ => Y) R) :
    (T.filter ((clusterGraph inc X).Adj 0)).Nonempty ↔ ∃ i ∈ T, lnk inc Y (X i) := by
  have hX0 : X 0 = Y := (mem_Fn.mp hX) 0 h0
  constructor
  · rintro ⟨w, hw⟩
    rw [Finset.mem_filter, clusterGraph_adj, hX0] at hw
    exact ⟨w, hw.1, hw.2.2⟩
  · rintro ⟨w, hw, h⟩
    refine ⟨w, Finset.mem_filter.mpr ⟨hw, ?_⟩⟩
    rw [clusterGraph_adj, hX0]
    exact ⟨fun h' => h0 (h' ▸ hT hw), h⟩

theorem Zr_term (Y : P) (K : P → A) {R T : Finset (Fin (N + 1))} (h0 : (0 : Fin (N + 1)) ∉ R)
    (hT : T ⊆ R) :
    ∑ X ∈ Fn (fun _ => Y) R,
      ((-(if (T.filter ((clusterGraph inc X).Adj 0)).Nonempty then 1 else 0 : ℤ) : ℤ) : A) *
        (clusterUrsell inc X T : A) * (clusterUrsell inc X (insert 0 (R \ T)) : A) *
        ∏ i ∈ R, K (X i) = -(blkc inc Y K T.card) * Zr inc Y K (R \ T) := by
  have hdisj : Disjoint T (R \ T) := Finset.disjoint_sdiff
  have hR : R = T ∪ (R \ T) := (Finset.union_sdiff_of_subset hT).symm
  have h0' : (0 : Fin (N + 1)) ∉ R \ T := fun h => h0 (Finset.sdiff_subset h)
  rw [show Fn (fun _ => Y) R = Fn (fun _ => Y) (T ∪ (R \ T)) from by rw [← hR], sum_Fn_union _ hdisj, ← blk_eq inc Y K T, Zr, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun X hX => ?_)
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun X' hX' => ?_)
  have hX1 : X ∈ Fn (fun _ => Y) R := by
    rw [mem_Fn] at hX ⊢
    intro i hi
    exact hX i (fun h => hi (hT h))
  have hZ : merge T X X' ∈ Fn (fun _ => Y) R := by
    rw [mem_Fn] at hX hX' ⊢
    intro i hi
    by_cases hiT : i ∈ T
    · exact absurd (hT hiT) hi
    · simp only [merge, hiT, ite_false]
      exact hX' i (fun h => hi (by rw [hR]; exact Finset.mem_union_right _ h))
  have e1 : (T.filter ((clusterGraph inc (merge T X X')).Adj 0)).Nonempty ↔
      ∃ i ∈ T, lnk inc Y (X i) := by
    rw [adj_root inc h0 hT hZ]
    constructor
    · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by simpa [merge, hi] using h⟩
    · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by simpa [merge, hi] using h⟩
  have e2 : clusterUrsell inc (merge T X X') T = clusterUrsell inc X T :=
    clusterUrsell_congr inc (fun i hi => by simp [merge, hi])
  have e3 : clusterUrsell inc (merge T X X') (insert 0 (R \ T)) =
      clusterUrsell inc X' (insert 0 (R \ T)) := by
    refine clusterUrsell_congr inc (fun i hi => ?_)
    have : i ∉ T := by
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact fun h => h0 (hT h)
      · exact (Finset.mem_sdiff.mp hi').2
    simp [merge, this]
  have e4 : ∏ i ∈ R, K (merge T X X' i) = (∏ i ∈ T, K (X i)) * ∏ i ∈ R \ T, K (X' i) := by
    rw [← Finset.prod_sdiff hT, mul_comm]
    congr 1
    · exact Finset.prod_congr rfl (fun i hi => by simp [merge, hi])
    · refine Finset.prod_congr rfl (fun i hi => ?_)
      have : i ∉ T := (Finset.mem_sdiff.mp hi).2
      simp [merge, this]
  rw [e2, e3, e4]
  simp only [e1, Int.cast_neg, Int.cast_ite, Int.cast_one, Int.cast_zero]
  ring_nf

theorem sum_powerset_contains {B : Type*} [AddCommMonoid B] (R : Finset (Fin (N + 1))) {u0 : Fin (N + 1)}
    (hu0 : u0 ∈ R) (F : ℕ → B) :
    ∑ T ∈ R.powerset.filter (fun T => u0 ∈ T), F T.card =
      ∑ j ∈ Finset.range R.card, (R.card - 1).choose j • F (j + 1) := by
  have h1 : ∑ T ∈ R.powerset.filter (fun T => u0 ∈ T), F T.card =
      ∑ T' ∈ (R.erase u0).powerset, F (T'.card + 1) := by
    refine Finset.sum_nbij' (fun T => T.erase u0) (fun T' => insert u0 T') ?_ ?_ ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_filter, Finset.mem_powerset] at hT
      rw [Finset.mem_powerset]
      exact Finset.erase_subset_erase _ hT.1
    · intro T' hT'
      rw [Finset.mem_powerset] at hT'
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset hu0 (hT'.trans (Finset.erase_subset _ _)), Finset.mem_insert_self _ _⟩
    · intro T hT
      rw [Finset.mem_filter] at hT
      exact Finset.insert_erase hT.2
    · intro T' hT'
      rw [Finset.mem_powerset] at hT'
      exact Finset.erase_insert (fun h => (Finset.notMem_erase u0 R) (hT' h))
    · intro T hT
      rw [Finset.mem_filter] at hT
      rw [Finset.card_erase_of_mem hT.2]
      have : 1 ≤ T.card := Finset.card_pos.mpr ⟨u0, hT.2⟩
      congr 1; omega
  rw [h1, Finset.sum_powerset_apply_card (fun m => F (m + 1))]
  have hc : (R.erase u0).card = R.card - 1 := Finset.card_erase_of_mem hu0
  have hpos : 0 < R.card := Finset.card_pos.mpr ⟨u0, hu0⟩
  rw [hc, show R.card = R.card - 1 + 1 by omega]
  simp

theorem Zr_eq (Y : P) (K : P → A) :
    ∀ (n : ℕ) (R : Finset (Fin (N + 1))), (0 : Fin (N + 1)) ∉ R → R.card = n →
      Zr inc Y K R = ZZ (blkc inc Y K) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R h0 hcard
    rcases R.eq_empty_or_nonempty with rfl | ⟨u0, hu0⟩
    · have : n = 0 := by rw [← hcard]; rfl
      subst this
      rw [ZZ_zero, Zr, Fn_empty]
      simp [ursell_singleton, clusterUrsell]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := Finset.card_pos.mpr ⟨u0, hu0⟩; omega⟩
      have hrec : ∀ X : Fin (N + 1) → P, (clusterUrsell inc X (insert 0 R) : A) =
          ∑ T ∈ R.powerset.filter (fun T => u0 ∈ T),
            ((-(if (T.filter ((clusterGraph inc X).Adj 0)).Nonempty then 1 else 0 : ℤ) : ℤ) : A) *
              (clusterUrsell inc X T : A) * (clusterUrsell inc X (insert 0 (R \ T)) : A) := by
        intro X
        unfold clusterUrsell
        rw [ursell_insert_rec _ h0 hu0]
        push_cast
        rfl
      have step : Zr inc Y K R = ∑ T ∈ R.powerset.filter (fun T => u0 ∈ T),
          (-(blkc inc Y K T.card) * Zr inc Y K (R \ T)) := by
        rw [Zr]
        simp_rw [hrec, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun T hT => ?_)
        rw [Finset.mem_filter, Finset.mem_powerset] at hT
        exact Zr_term inc Y K h0 hT.1
      rw [step]
      have hZ : ∀ T ∈ R.powerset.filter (fun T => u0 ∈ T),
          (-(blkc inc Y K T.card) * Zr inc Y K (R \ T)) =
            -(blkc inc Y K T.card * ZZ (blkc inc Y K) (m + 1 - T.card)) := by
        intro T hT
        rw [Finset.mem_filter, Finset.mem_powerset] at hT
        have hTc : 1 ≤ T.card := Finset.card_pos.mpr ⟨u0, hT.2⟩
        have hlt : m + 1 - T.card < m + 1 := by omega
        rw [ih _ hlt (R \ T) (fun h => h0 (Finset.sdiff_subset h))
          (by rw [Finset.card_sdiff_of_subset hT.1, hcard]), neg_mul]
      rw [Finset.sum_congr rfl hZ, Finset.sum_neg_distrib,
        sum_powerset_contains R hu0 (fun k => blkc inc Y K k * ZZ (blkc inc Y K) (m + 1 - k)),
        hcard, ZZ_succ]
      congr 1
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      simp only [nsmul_eq_mul, Nat.add_sub_cancel]
      rw [show m + 1 - (j + 1) = m - j by omega]
      ring

end RootedSum

end Balaban.Polymer
