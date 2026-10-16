module

public import Balaban.Polymer.Bridge

/-!
# The chain from a polymer near the edge of the quarter box to the outside (W843, blocker 7)

Cells of the last scale are the sites of the block torus `Torus d K` (`K` cells per side).  The
box of radius `r` is the set of cells all of whose coordinates `v` satisfy `v ≤ r` or
`K - r ≤ v` (distance at most `r` from the origin on the cyclic line), and a cell is outside the
box of radius `r` when some coordinate satisfies `r < v < K - r`.

A polymer `Y` of cells in the box that contains a cell whose coordinate `μ₀` is within `t` of the
edge (`r ≤ v + t` on the positive side, `r ≤ K - v + t` on the negative side) is joined to the
outside of the box by the straight chain of cells in the direction `μ₀` that leaves the box.
The chain has at most `t + 1` cells besides the starting cell, so `Y' = Y ∪ chain` is a polymer
with `|Y'| ≤ |Y| + t + 1` cells.  The map `Y ↦ Y'` is a function of `Y`, with `Y ⊆ Y'`; hence
each `Y'` has at most `2 ^ |Y'|` preimages.  `exists_edgeChain_map` is the statement for the
block torus, `edgeChain_isPolymer` the same for the frozen polymers of block side `s`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section Chain

variable {d K : ℕ} [NeZero K]

omit [NeZero K] in
theorem animal_union_path {Y : Finset (Balaban.Torus d K)} (hY : IsAnimal (blockGraph d K) Y)
    (q : ℕ → Balaban.Torus d K) (n : ℕ) (h0 : q 0 ∈ Y)
    (hadj : ∀ j < n, (blockGraph d K).Adj (q j) (q (j + 1))) :
    IsAnimal (blockGraph d K) (Y ∪ (Finset.range (n + 1)).image q) := by
  set U := Y ∪ (Finset.range (n + 1)).image q with hU
  have hYU : Y ⊆ U := Finset.subset_union_left
  have hqU : ∀ j ≤ n, q j ∈ U := fun j hj =>
    Finset.mem_union_right _ (Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩)
  have hpath : ∀ j, j ≤ n → Relation.ReflTransGen
      (fun a b => a ∈ U ∧ b ∈ U ∧ (blockGraph d K).Adj a b) (q 0) (q j) := by
    intro j
    induction j with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ j ih =>
      intro hj
      exact Relation.ReflTransGen.tail (ih (by omega))
        ⟨hqU j (by omega), hqU (j + 1) hj, hadj j (by omega)⟩
  have hreach : ∀ x ∈ U, Relation.ReflTransGen
      (fun a b => a ∈ U ∧ b ∈ U ∧ (blockGraph d K).Adj a b) (q 0) x := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · have := ((isAnimal_iff _ _).1 hY).2 _ h0 _ hx
      exact Relation.ReflTransGen.mono
        (p := fun a b => a ∈ U ∧ b ∈ U ∧ (blockGraph d K).Adj a b)
        (fun a b ⟨ha, hb, hab⟩ => ⟨hYU ha, hYU hb, hab⟩) _ _ this
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      have hj' : j ≤ n := by have := Finset.mem_range.1 hj; omega
      exact hpath j hj'
  rw [isAnimal_iff]
  refine ⟨⟨q 0, hYU h0⟩, fun x hx y hy => ?_⟩
  have hsymm : Std.Symm (fun a b => a ∈ U ∧ b ∈ U ∧ (blockGraph d K).Adj a b) :=
    ⟨fun a b ⟨ha, hb, hab⟩ => ⟨hb, ha, hab.symm⟩⟩
  exact (Std.Symm.symm _ _ (hreach x hx)).trans (hreach y hy)

omit [NeZero K] in
theorem adj_add_single (hK : K ≠ 1) (a : Balaban.Torus d K) (μ : Fin d) :
    (blockGraph d K).Adj a (a + Pi.single μ 1) := by
  have : Nontrivial (ZMod K) := ZMod.nontrivial_iff.2 hK
  refine ⟨?_, μ, Or.inl rfl⟩
  intro h
  have := congrFun h μ
  simp at this

omit [NeZero K] in
theorem adj_sub_single (hK : K ≠ 1) (a : Balaban.Torus d K) (μ : Fin d) :
    (blockGraph d K).Adj a (a - Pi.single μ 1) := by
  have := adj_add_single hK (a - Pi.single μ 1) μ
  rw [sub_add_cancel] at this
  exact this.symm

omit [NeZero K] in
theorem exists_path_pos (hK : K ≠ 1) (b0 : Balaban.Torus d K) (μ : Fin d) :
    ∃ q : ℕ → Balaban.Torus d K, q 0 = b0 ∧
      (∀ j, (blockGraph d K).Adj (q j) (q (j + 1))) ∧ ∀ j, q j μ = b0 μ + (j : ZMod K) := by
  refine ⟨fun j => b0 + Pi.single μ (j : ZMod K), by simp, fun j => ?_, fun j => by simp⟩
  have : b0 + Pi.single μ (((j + 1 : ℕ)) : ZMod K) =
      (b0 + Pi.single μ (j : ZMod K)) + Pi.single μ 1 := by
    rw [Nat.cast_succ, Pi.single_add, add_assoc]
  show (blockGraph d K).Adj (b0 + Pi.single μ (j : ZMod K)) (b0 + Pi.single μ (((j + 1 : ℕ)) : ZMod K))
  rw [this]
  exact adj_add_single hK _ μ

omit [NeZero K] in
theorem exists_path_neg (hK : K ≠ 1) (b0 : Balaban.Torus d K) (μ : Fin d) :
    ∃ q : ℕ → Balaban.Torus d K, q 0 = b0 ∧
      (∀ j, (blockGraph d K).Adj (q j) (q (j + 1))) ∧ ∀ j, q j μ = b0 μ - (j : ZMod K) := by
  refine ⟨fun j => b0 - Pi.single μ (j : ZMod K), by simp, fun j => ?_, fun j => by simp⟩
  have : b0 - Pi.single μ (((j + 1 : ℕ)) : ZMod K) =
      (b0 - Pi.single μ (j : ZMod K)) - Pi.single μ 1 := by
    rw [Nat.cast_succ, Pi.single_add, sub_add_eq_sub_sub]
  show (blockGraph d K).Adj (b0 - Pi.single μ (j : ZMod K)) (b0 - Pi.single μ (((j + 1 : ℕ)) : ZMod K))
  rw [this]
  exact adj_sub_single hK _ μ

/-- The straight chain leaving the box of radius `r` in the direction `μ₀`, from a cell whose
coordinate `μ₀` is within `t` of the edge. -/
theorem exists_exit_path {r t : ℕ} (hK : 2 * r + 2 ≤ K) (b0 : Balaban.Torus d K) (μ₀ : Fin d)
    (hnear : ((b0 μ₀).val ≤ r ∧ r ≤ (b0 μ₀).val + t) ∨
      (K - r ≤ (b0 μ₀).val ∧ r ≤ K - (b0 μ₀).val + t)) :
    ∃ (q : ℕ → Balaban.Torus d K) (n : ℕ), q 0 = b0 ∧ n ≤ t + 1 ∧
      (∀ j < n, (blockGraph d K).Adj (q j) (q (j + 1))) ∧
      r < (q n μ₀).val ∧ (q n μ₀).val < K - r := by
  have hK1 : K ≠ 1 := by omega
  have hvK := ZMod.val_lt (b0 μ₀)
  have hb : b0 μ₀ = (((b0 μ₀).val : ℕ) : ZMod K) := (ZMod.natCast_zmod_val _).symm
  rcases hnear with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨q, hq0, hqa, hqv⟩ := exists_path_pos hK1 b0 μ₀
    refine ⟨q, r + 1 - (b0 μ₀).val, hq0, by omega, fun j _ => hqa j, ?_⟩
    have : q (r + 1 - (b0 μ₀).val) μ₀ = (((b0 μ₀).val + (r + 1 - (b0 μ₀).val) : ℕ) : ZMod K) := by
      rw [hqv, Nat.cast_add]
      congr 1
    rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    omega
  · obtain ⟨q, hq0, hqa, hqv⟩ := exists_path_neg hK1 b0 μ₀
    refine ⟨q, (b0 μ₀).val + r + 1 - K, hq0, by omega, fun j _ => hqa j, ?_⟩
    have : q ((b0 μ₀).val + r + 1 - K) μ₀ =
        (((b0 μ₀).val - ((b0 μ₀).val + r + 1 - K) : ℕ) : ZMod K) := by
      rw [hqv]
      calc b0 μ₀ - (((b0 μ₀).val + r + 1 - K : ℕ) : ZMod K)
          = (((b0 μ₀).val : ℕ) : ZMod K) - (((b0 μ₀).val + r + 1 - K : ℕ) : ZMod K) := by
            rw [ZMod.natCast_zmod_val]
        _ = _ := (Nat.cast_sub (by omega)).symm
    rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    omega

omit [NeZero K] in
theorem card_union_path_le {Y : Finset (Balaban.Torus d K)} (q : ℕ → Balaban.Torus d K) (n : ℕ)
    (h0 : q 0 ∈ Y) :
    (Y ∪ (Finset.range (n + 1)).image q).card ≤ Y.card + n := by
  have : Y ∪ (Finset.range (n + 1)).image q = Y ∪ (Finset.Ico 1 (n + 1)).image q := by
    ext x
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro (h | ⟨j, hj, rfl⟩)
      · exact Or.inl h
      · by_cases hj0 : j = 0
        · subst hj0; exact Or.inl h0
        · exact Or.inr ⟨j, ⟨by omega, hj⟩, rfl⟩
    · rintro (h | ⟨j, hj, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, rfl⟩
  rw [this]
  refine (Finset.card_union_le _ _).trans ?_
  have := Finset.card_image_le (s := Finset.Ico 1 (n + 1)) (f := q)
  rw [Nat.card_Ico] at this
  omega

/-- **Chain geometry (W843, blocker 7).**  There is a map `Φ` on sets of cells such that for
every polymer `Y` of the block torus inside the box of radius `r` (`2r + 2 ≤ K`) and containing a
cell `b₀` whose coordinate `μ₀` lies within `t` of the edge of the box, `Φ Y` is a polymer
containing `Y`, with at most `t + 1` more cells than `Y`, and with a cell outside the box.  Every
set `Z` has at most `2 ^ |Z|` preimages `Y` of this kind. -/
theorem exists_edgeChain_map {r t : ℕ} (hK : 2 * r + 2 ≤ K) :
    ∃ Φ : Finset (Balaban.Torus d K) → Finset (Balaban.Torus d K),
      (∀ Y : Finset (Balaban.Torus d K), IsAnimal (blockGraph d K) Y →
        (∀ b ∈ Y, ∀ μ, (b μ).val ≤ r ∨ K - r ≤ (b μ).val) →
        (∃ b0 ∈ Y, ∃ μ₀ : Fin d, ((b0 μ₀).val ≤ r ∧ r ≤ (b0 μ₀).val + t) ∨
          (K - r ≤ (b0 μ₀).val ∧ r ≤ K - (b0 μ₀).val + t)) →
        Y ⊆ Φ Y ∧ IsAnimal (blockGraph d K) (Φ Y) ∧ (Φ Y).card ≤ Y.card + (t + 1) ∧
          ∃ b ∈ Φ Y, ∃ μ : Fin d, r < (b μ).val ∧ (b μ).val < K - r) ∧
      ∀ Z : Finset (Balaban.Torus d K),
        ((Finset.univ : Finset (Finset (Balaban.Torus d K))).filter (fun Y =>
          IsAnimal (blockGraph d K) Y ∧
          (∀ b ∈ Y, ∀ μ, (b μ).val ≤ r ∨ K - r ≤ (b μ).val) ∧
          (∃ b0 ∈ Y, ∃ μ₀ : Fin d, ((b0 μ₀).val ≤ r ∧ r ≤ (b0 μ₀).val + t) ∨
            (K - r ≤ (b0 μ₀).val ∧ r ≤ K - (b0 μ₀).val + t)) ∧ Φ Y = Z)).card ≤
          2 ^ Z.card := by
  have key : ∀ Y : Finset (Balaban.Torus d K), IsAnimal (blockGraph d K) Y →
      (∀ b ∈ Y, ∀ μ, (b μ).val ≤ r ∨ K - r ≤ (b μ).val) →
      (∃ b0 ∈ Y, ∃ μ₀ : Fin d, ((b0 μ₀).val ≤ r ∧ r ≤ (b0 μ₀).val + t) ∨
        (K - r ≤ (b0 μ₀).val ∧ r ≤ K - (b0 μ₀).val + t)) →
      ∃ Z : Finset (Balaban.Torus d K), Y ⊆ Z ∧ IsAnimal (blockGraph d K) Z ∧
        Z.card ≤ Y.card + (t + 1) ∧ ∃ b ∈ Z, ∃ μ : Fin d, r < (b μ).val ∧ (b μ).val < K - r := by
    intro Y hY _ ⟨b0, hb0, μ₀, hnear⟩
    obtain ⟨q, n, hq0, hn, hadj, hr1, hr2⟩ := exists_exit_path hK b0 μ₀ hnear
    refine ⟨Y ∪ (Finset.range (n + 1)).image q, Finset.subset_union_left,
      animal_union_path hY q n (hq0 ▸ hb0) hadj, ?_, q n, ?_, μ₀, hr1, hr2⟩
    · have := card_union_path_le (Y := Y) q n (hq0 ▸ hb0)
      omega
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩)
  choose! Φ hΦ using key
  refine ⟨Φ, fun Y h1 h2 h3 => ?_, fun Z => ?_⟩
  · exact hΦ Y h1 h2 h3
  · have hsub : ((Finset.univ : Finset (Finset (Balaban.Torus d K))).filter (fun Y =>
          IsAnimal (blockGraph d K) Y ∧
          (∀ b ∈ Y, ∀ μ, (b μ).val ≤ r ∨ K - r ≤ (b μ).val) ∧
          (∃ b0 ∈ Y, ∃ μ₀ : Fin d, ((b0 μ₀).val ≤ r ∧ r ≤ (b0 μ₀).val + t) ∨
            (K - r ≤ (b0 μ₀).val ∧ r ≤ K - (b0 μ₀).val + t)) ∧ Φ Y = Z)) ⊆ Z.powerset := by
      intro Y hY
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY
      obtain ⟨h1, h2, h3, rfl⟩ := hY
      exact Finset.mem_powerset.2 (hΦ Y h1 h2 h3).1
    exact (Finset.card_le_card hsub).trans (by rw [Finset.card_powerset])

/-- The same in the frozen language: the union of the blocks of side `s` of `Φ Y` is a
`Balaban.IsPolymer`, contains the union of the blocks of `Y`, and its size `|X'| / s ^ d` is at
most `|Y| + t + 1`. -/
theorem edgeChain_isPolymer {s t : ℕ} [NeZero s] (Y Z : Finset (Balaban.Torus d K))
    (hZ : IsAnimal (blockGraph d K) Z) (hYZ : Y ⊆ Z) (hcard : Z.card ≤ Y.card + (t + 1)) :
    Balaban.IsPolymer d (s * K) s (siteSet d s K Z) ∧ siteSet d s K Y ⊆ siteSet d s K Z ∧
      ((siteSet d s K Z).card : ℝ) / (s : ℝ) ^ d ≤ (Y.card : ℝ) + (t + 1) := by
  refine ⟨(isPolymer_siteSet_iff Z).2 hZ, ?_, ?_⟩
  · intro x hx
    rw [mem_siteSet] at hx ⊢
    exact hYZ hx
  · have hs : (s : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne s)
    rw [card_siteSet]
    push_cast
    rw [mul_comm, mul_div_assoc, div_self hs, mul_one]
    exact_mod_cast hcard

end Chain

end Balaban.Polymer
