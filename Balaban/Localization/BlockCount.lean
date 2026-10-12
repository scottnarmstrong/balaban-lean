/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.TreeLengthCov
public import Balaban.LargeField.Geometry.Coarsen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The block count (LOCALIZATION.md §4.0 (iii), version 3)

A connected structure with `|E|` bonds meets at most `3^d (|E| / a + 1)` cells of side `a`
(`card_cells_le`): the argument is a discrete intermediate-value count.  For a cell `γ` met by the
structure, either the structure lies in the ball of radius `a - 1` around a point of `γ` (then it
meets at most `3^d` cells), or a path leaves the ball of radius `a`, and crosses the `a` levels
of the distance to the point, using `a` distinct bonds inside the ball; a bond lies in the ball
of at most `3^d` cells.

* `cellCount a X`: the number of cells of side `a` contained in `X`;
* `cellCount_le_of_chosen`: `cellCount ≤ L^{2d} · #(cells met)` for a chosen family;
* `blockCount_one`: the single-scale block count `n_j(X) ≤ L^{2d} 3^d (d^cov_j(X) + 1)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Finset

section Crossing

variable {α : Type*}

/-- Discrete intermediate-value theorem along a connected structure: if the function `g` changes
by at most `1` along every bond, `g x = 0` and `t < g y`, then some bond crosses from level `t` to
level `t + 1`. -/
theorem crossing_edge (g : α → ℕ) (W : Finset α) (E : Finset (α × α))
    (hconn : ∀ x ∈ W, ∀ y ∈ W, Relation.ReflTransGen (fun a b => (a, b) ∈ E ∨ (b, a) ∈ E) x y)
    (hLip : ∀ p ∈ E, g p.1 ≤ g p.2 + 1 ∧ g p.2 ≤ g p.1 + 1) {x y : α} (hx : x ∈ W) (hy : y ∈ W)
    (hgx : g x = 0) :
    ∀ t < g y, ∃ p ∈ E, (g p.1 = t ∧ g p.2 = t + 1) ∨ (g p.2 = t ∧ g p.1 = t + 1) := by
  have h := hconn x hx y hy
  clear hy
  induction h with
  | refl => intro t ht; omega
  | @tail b c _ hbc ih =>
    intro t ht
    rcases hbc with hbc | hbc
    · have hl := hLip _ hbc
      by_cases htb : t < g b
      · exact ih t htb
      · refine ⟨(b, c), hbc, Or.inl ⟨?_, ?_⟩⟩ <;> simp only at hl ⊢ <;> omega
    · have hl := hLip _ hbc
      by_cases htb : t < g b
      · exact ih t htb
      · refine ⟨(c, b), hbc, Or.inr ⟨?_, ?_⟩⟩ <;> simp only at hl ⊢ <;> omega

/-- If the structure leaves the sublevel set `{g ≤ R - 1}`, then at least `R` bonds lie in
`{g ≤ R}`. -/
theorem card_edges_ge (g : α → ℕ) (W : Finset α) (E : Finset (α × α))
    (hconn : ∀ x ∈ W, ∀ y ∈ W, Relation.ReflTransGen (fun a b => (a, b) ∈ E ∨ (b, a) ∈ E) x y)
    (hLip : ∀ p ∈ E, g p.1 ≤ g p.2 + 1 ∧ g p.2 ≤ g p.1 + 1) {x y : α} (hx : x ∈ W) (hy : y ∈ W)
    (hgx : g x = 0) (R : ℕ) (hR : R ≤ g y) :
    R ≤ (E.filter fun p => g p.1 ≤ R ∧ g p.2 ≤ R).card := by
  classical
  have hsub : Finset.range R ⊆
      (E.filter fun p => g p.1 ≤ R ∧ g p.2 ≤ R).image fun p => min (g p.1) (g p.2) := by
    intro t ht
    rw [Finset.mem_range] at ht
    obtain ⟨p, hp, hc⟩ := crossing_edge g W E hconn hLip hx hy hgx t (by omega)
    rw [Finset.mem_image]
    refine ⟨p, Finset.mem_filter.2 ⟨hp, ?_⟩, ?_⟩
    · omega
    · omega
  calc R = (Finset.range R).card := (Finset.card_range R).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le

end Crossing

section Cells

variable {d n m a : ℕ}

theorem cycNorm_one_le [NeZero n] : LargeField.cycNorm n (1 : ZMod n) ≤ 1 :=
  (LargeField.cycNorm_le_iff (1 : ZMod n) 1).2 ⟨1, by simp, by simp⟩

theorem supDist_nbr [NeZero n] {x y : Torus d n} (h : Nbr x y) : LargeField.supDist x y ≤ 1 := by
  obtain ⟨μ, h | h⟩ := h
  · refine LargeField.supDist_le_iff.2 fun i => ?_
    rw [h]
    by_cases hi : i = μ
    · subst hi; simpa using (LargeField.cycNorm_neg (n := n) 1).le.trans cycNorm_one_le
    · simp [hi, LargeField.cycNorm]
  · refine LargeField.supDist_le_iff.2 fun i => ?_
    rw [h]
    by_cases hi : i = μ
    · subst hi; simpa using cycNorm_one_le
    · simp [hi, LargeField.cycNorm]

/-- The ball of radius `1` in the index distance has at most `3^d` points. -/
theorem card_ball_one [NeZero m] (x : Torus d m) :
    (Finset.univ.filter fun y : Torus d m => LargeField.supDist y x ≤ 1).card ≤ 3 ^ d := by
  classical
  have hsub : (Finset.univ.filter fun y : Torus d m => LargeField.supDist y x ≤ 1) ⊆
      Fintype.piFinset (fun i => ({x i, x i + 1, x i - 1} : Finset (ZMod m))) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [Fintype.mem_piFinset]
    intro i
    have h := LargeField.supDist_le_iff.1 hy i
    obtain ⟨t, ht, hte⟩ := (LargeField.cycNorm_le_iff _ 1).1 h
    have ht' : t = -1 ∨ t = 0 ∨ t = 1 := by
      have := abs_le.1 (by simpa using ht : |t| ≤ 1); omega
    have hyi : y i = x i + t := by rw [hte]; ring
    rcases ht' with rfl | rfl | rfl <;> simp [hyi, sub_eq_add_neg]
  calc _ ≤ (Fintype.piFinset (fun i => ({x i, x i + 1, x i - 1} : Finset (ZMod m)))).card :=
        Finset.card_le_card hsub
    _ = ∏ i : Fin d, ({x i, x i + 1, x i - 1} : Finset (ZMod m)).card := Fintype.card_piFinset _
    _ ≤ 3 ^ (Finset.univ : Finset (Fin d)).card :=
        Finset.prod_le_pow_card _ _ _ fun i _ => Finset.card_le_three
    _ = 3 ^ d := by simp

end Cells

section CellCount

variable {d n m a : ℕ} [NeZero n] [NeZero m]

theorem div_le_one_of_lt (ha : 0 < a) {r : ℕ} (h : r + a - 1 < 2 * a) : (r + a - 1) / a ≤ 1 := by
  have : (r + a - 1) / a < 2 := (Nat.div_lt_iff_lt_mul ha).2 (by omega)
  omega

/-- **A connected structure with `|E|` bonds meets few cells**: `a · #(cells met) ≤ 3^d (|E| + a)`. -/
theorem card_cells_le (hn : n = a * m) (ha : 0 < a) {W : Finset (Torus d n)}
    {E : Finset (Torus d n × Torus d n)} (hc : ConnStruct W E) :
    a * (W.image (blockMap a m)).card ≤ 3 ^ d * (E.card + a) := by
  classical
  obtain ⟨hne, hE, hconn⟩ := hc
  set Γ := W.image (blockMap a m) with hΓ
  have hβ : ∀ x y : Torus d n, LargeField.supDist (blockMap a m x) (blockMap a m y) ≤
      (LargeField.supDist x y + a - 1) / a := fun x y => LargeField.supDist_blockMap_le hn x y
  by_cases hA : ∃ x ∈ W, ∀ y ∈ W, LargeField.supDist y x ≤ a - 1
  · obtain ⟨x, hx, hall⟩ := hA
    have hsub : Γ ⊆ Finset.univ.filter fun γ : Torus d m =>
        LargeField.supDist γ (blockMap a m x) ≤ 1 := by
      intro γ hγ
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hγ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine (hβ y x).trans (div_le_one_of_lt ha ?_)
      have := hall y hy; omega
    have h1 := (Finset.card_le_card hsub).trans (card_ball_one (blockMap a m x))
    calc a * Γ.card ≤ a * 3 ^ d := Nat.mul_le_mul_left _ h1
      _ ≤ 3 ^ d * (E.card + a) := by nlinarith [Nat.zero_le (3 ^ d * E.card)]
  · push Not at hA
    have hrep : ∀ γ : Torus d m, ∃ x : Torus d n, γ ∈ Γ → (x ∈ W ∧ blockMap a m x = γ) := by
      intro γ
      by_cases h : γ ∈ Γ
      · obtain ⟨x, hx, hxγ⟩ := Finset.mem_image.1 h
        exact ⟨x, fun _ => ⟨hx, hxγ⟩⟩
      · exact ⟨0, fun h' => absurd h' h⟩
    choose s hs using hrep
    let Q : Torus d m → Torus d n × Torus d n → Prop := fun γ p =>
      LargeField.supDist p.1 (s γ) ≤ a ∧ LargeField.supDist p.2 (s γ) ≤ a
    have hcount : ∀ γ ∈ Γ, a ≤ (E.filter (Q γ)).card := by
      intro γ hγ
      obtain ⟨hsW, hsγ⟩ := hs γ hγ
      obtain ⟨y, hy, hya⟩ := hA (s γ) hsW
      refine card_edges_ge (fun z => LargeField.supDist z (s γ)) W E hconn ?_ hsW hy
        (LargeField.supDist_self _) a (by omega)
      intro p hp
      obtain ⟨-, -, hnb⟩ := hE p hp
      have h1 := supDist_nbr hnb
      have t1 := LargeField.supDist_triangle p.1 p.2 (s γ)
      have t2 := LargeField.supDist_triangle p.2 p.1 (s γ)
      rw [LargeField.supDist_comm p.2 p.1] at t2
      exact ⟨by omega, by omega⟩
    have hdouble : ∑ γ ∈ Γ, (E.filter (Q γ)).card = ∑ p ∈ E, (Γ.filter fun γ => Q γ p).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    have hper : ∀ p ∈ E, (Γ.filter fun γ => Q γ p).card ≤ 3 ^ d := by
      intro p hp
      refine le_trans (Finset.card_le_card ?_) (card_ball_one (blockMap a m p.1))
      intro γ hγ
      obtain ⟨hγΓ, hQ⟩ := Finset.mem_filter.1 hγ
      obtain ⟨-, hsγ⟩ := hs γ hγΓ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [LargeField.supDist_comm, ← hsγ]
      exact (hβ p.1 (s γ)).trans (div_le_one_of_lt ha (by have := hQ.1; omega))
    calc a * Γ.card = ∑ _γ ∈ Γ, a := by simp [mul_comm]
      _ ≤ ∑ γ ∈ Γ, (E.filter (Q γ)).card := Finset.sum_le_sum hcount
      _ = ∑ p ∈ E, (Γ.filter fun γ => Q γ p).card := hdouble
      _ ≤ ∑ _p ∈ E, 3 ^ d := Finset.sum_le_sum hper
      _ = E.card * 3 ^ d := by simp
      _ ≤ 3 ^ d * (E.card + a) := by nlinarith [Nat.zero_le (3 ^ d * a), Nat.zero_le (3 ^ d)]

end CellCount

section Chosen

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

open Classical in
/-- The number of cells of side `a` (aligned boxes `box b a`) contained in `X`. -/
noncomputable def cellCount (a : ℕ) (X : Set (CTorus d L N₁ m₁ K)) : ℕ :=
  (Finset.univ.filter fun b : CTorus d L N₁ m₁ K => Aligned a b ∧ box b a ⊆ X).card

open Classical in
/-- An aligned cube `box b' (L a)` contains at most `L^d` aligned points. -/
theorem card_aligned_in_cube {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (ha0 : 0 < a)
    {b' : CTorus d L N₁ m₁ K} (hb' : Aligned a b') :
    (Finset.univ.filter fun b : CTorus d L N₁ m₁ K => Aligned a b ∧ b ∈ box b' (L * a)).card ≤
      L ^ d := by
  classical
  have hsub : (Finset.univ.filter fun b : CTorus d L N₁ m₁ K => Aligned a b ∧ b ∈ box b' (L * a)) ⊆
      (Fintype.piFinset fun _ : Fin d => Finset.range L).image
        (fun t : Fin d → ℕ => b' + natT (fun μ => a * t μ)) := by
    intro b hb
    obtain ⟨hal, w, hw, rfl⟩ := (Finset.mem_filter.1 hb).2
    rw [Finset.mem_image]
    refine ⟨fun μ => w μ / a, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro μ
      rw [Finset.mem_range, Nat.div_lt_iff_lt_mul ha0]
      have := hw μ; linarith [mul_comm L a]
    · have hmod : ∀ μ, w μ % a = 0 := fun μ => by
        have := hal μ
        rwa [mod_of_aligned_add ha hb' μ] at this
      congr 2
      funext μ
      have := Nat.div_add_mod (w μ) a
      rw [hmod μ] at this
      omega
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Fintype.piFinset fun _ : Fin d => Finset.range L).card := Finset.card_image_le
    _ = L ^ d := by simp

open Classical in
/-- A cell `γ` lies in at most `L^d` aligned cubes `box b' (L a)`. -/
theorem card_cubes_containing {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (ha0 : 0 < a)
    {γ : CTorus d L N₁ m₁ K} (hγ : Aligned a γ) :
    (Finset.univ.filter fun b' : CTorus d L N₁ m₁ K => Aligned a b' ∧ γ ∈ box b' (L * a)).card ≤
      L ^ d := by
  classical
  have hsub : (Finset.univ.filter fun b' : CTorus d L N₁ m₁ K =>
      Aligned a b' ∧ γ ∈ box b' (L * a)) ⊆
      (Fintype.piFinset fun _ : Fin d => Finset.range L).image
        (fun t : Fin d → ℕ => γ - natT (fun μ => a * t μ)) := by
    intro b' hb'
    obtain ⟨hal, w, hw, hγw⟩ := (Finset.mem_filter.1 hb').2
    rw [Finset.mem_image]
    have hmod : ∀ μ, w μ % a = 0 := fun μ => by
      have := hγ μ
      rw [hγw, mod_of_aligned_add ha hal μ] at this
      exact this
    refine ⟨fun μ => w μ / a, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro μ
      rw [Finset.mem_range, Nat.div_lt_iff_lt_mul ha0]
      have := hw μ; linarith [mul_comm L a]
    · have : (fun μ => a * (w μ / a)) = w := by
        funext μ
        have := Nat.div_add_mod (w μ) a
        rw [hmod μ] at this
        omega
      rw [this, hγw]; abel
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Fintype.piFinset fun _ : Fin d => Finset.range L).card := Finset.card_image_le
    _ = L ^ d := by simp

/-- **Cells versus cells met**: if `𝒦` is a family of aligned cubes of side `L a` covering `X`,
and `W` meets every cube of `𝒦`, then `X` contains at most `L^{2d}` times as many cells as the
number of cells met by `W`. -/
theorem cellCount_le {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (ha0 : 0 < a)
    {X : Set (CTorus d L N₁ m₁ K)} {𝒦 : Set (CTorus d L N₁ m₁ K)}
    (hK : ∀ b ∈ 𝒦, Aligned a b) (hcov : ∀ z ∈ X, ∃ b ∈ 𝒦, z ∈ box b (L * a))
    {W : Finset (CTorus d L N₁ m₁ K)} (hmeet : ∀ b ∈ 𝒦, ∃ x ∈ W, x ∈ box b (L * a)) :
    cellCount a X ≤ L ^ d * L ^ d * (W.image (cbase a)).card := by
  classical
  unfold cellCount
  set S := Finset.univ.filter fun b : CTorus d L N₁ m₁ K => Aligned a b ∧ box b a ⊆ X with hS
  have hf : ∀ b ∈ S, ∃ b' ∈ 𝒦, b ∈ box b' (L * a) := by
    intro b hb
    obtain ⟨-, hbX⟩ := (Finset.mem_filter.1 hb).2
    exact hcov b (hbX (mem_box_self b ha0))
  have hg : ∀ b ∈ S, ∃ b' ∈ 𝒦, b ∈ box b' (L * a) ∧ ∃ x ∈ W, x ∈ box b' (L * a) :=
    fun b hb => by
      obtain ⟨b', hb', hbb'⟩ := hf b hb
      exact ⟨b', hb', hbb', hmeet b' hb'⟩
  -- the map `b ↦ cbase a x_b`
  have hex : ∀ b : CTorus d L N₁ m₁ K, ∃ g : CTorus d L N₁ m₁ K, b ∈ S →
      ∃ b' ∈ 𝒦, b ∈ box b' (L * a) ∧ ∃ x ∈ W, x ∈ box b' (L * a) ∧ g = cbase a x := by
    intro b
    by_cases hb : b ∈ S
    · obtain ⟨b', hb', hbb', x, hx, hxb'⟩ := hg b hb
      exact ⟨cbase a x, fun _ => ⟨b', hb', hbb', x, hx, hxb', rfl⟩⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose g hgS using hex
  have himg : S.image g ⊆ W.image (cbase a) := by
    intro γ hγ
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨b', -, -, x, hx, -, hgx⟩ := hgS b hb
    exact Finset.mem_image.2 ⟨x, hx, hgx.symm⟩
  have hfib : ∀ γ ∈ S.image g, (S.filter fun b => g b = γ).card ≤ L ^ d * L ^ d := by
    intro γ hγ
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.1 hγ
    set γ := g b₀ with hγdef
    -- γ is aligned, being a `cbase`
    obtain ⟨-, -, -, x₀, -, -, hgx₀⟩ := hgS b₀ hb₀
    have hγal : Aligned a γ := by
      have e : γ = cbase a x₀ := hgx₀
      rw [e]; exact aligned_cbase x₀
    let B : Finset (CTorus d L N₁ m₁ K) :=
      Finset.univ.filter fun b' => Aligned a b' ∧ γ ∈ box b' (L * a)
    have hBcard : B.card ≤ L ^ d := card_cubes_containing ha ha0 hγal
    have hsub : (S.filter fun b => g b = γ) ⊆ B.biUnion fun b' =>
        Finset.univ.filter fun b : CTorus d L N₁ m₁ K => Aligned a b ∧ b ∈ box b' (L * a) := by
      intro b hb
      obtain ⟨hbS, hbg⟩ := Finset.mem_filter.1 hb
      obtain ⟨b', hb'K, hbb', x, hx, hxb', hgx⟩ := hgS b hbS
      rw [Finset.mem_biUnion]
      refine ⟨b', Finset.mem_filter.2 ⟨Finset.mem_univ _, hK b' hb'K, ?_⟩, ?_⟩
      · rw [← hbg, hgx]
        exact cell_subset_cube ha ha0 (hK b' hb'K) hxb' (mem_box_self _ ha0)
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hbS).2.1, hbb'⟩
    refine (Finset.card_le_card hsub).trans ?_
    refine (Finset.card_biUnion_le_card_mul _ _ (L ^ d) fun b' hb' => ?_).trans
      (Nat.mul_le_mul hBcard le_rfl)
    exact card_aligned_in_cube ha ha0 (Finset.mem_filter.1 hb').2.1
  calc S.card ≤ (L ^ d * L ^ d) * (S.image g).card :=
        Finset.card_le_mul_card_image S _ hfib
    _ ≤ (L ^ d * L ^ d) * (W.image (cbase a)).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card himg)

end Chosen

section SingleScale

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

/-- The cells met by a set `W` are counted equally by `cbase` and by the block map. -/
theorem card_cbase_le {n a m : ℕ} [NeZero n] [NeZero m] (hn : n = a * m) (W : Finset (Torus d n)) :
    (W.image (cbase a)).card ≤ (W.image (blockMap a m)).card := by
  classical
  let F : Torus d m → Torus d n := fun γ i => ((a * (γ i).val : ℕ) : ZMod n)
  have hF : W.image (cbase a) = (W.image (blockMap a m)).image F := by
    rw [Finset.image_image]
    refine Finset.image_congr fun z _ => ?_
    funext i
    simp only [Function.comp_apply, F, cbase, blockMap_apply, blockCoord_val hn]
  rw [hF]
  exact Finset.card_image_le

/-- **The single-scale block count** (LOCALIZATION.md §4.0 (iii), `X` a union of `π'_j`-cubes
of a chosen family): `n_j(X) ≤ L^{2d} 3^d (d^cov_j(X) + 1)`, where `n_j(X)` is the number of
`π_j`-cubes contained in `X`. -/
theorem blockCount_one {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {X : Set (CTorus d L N₁ m₁ K)}
    (hX : ∃ 𝒦 W E, ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W) :
    (cellCount (cellSide L m₀ m₁ j) X : ℝ) ≤
      (L : ℝ) ^ (2 * d) * 3 ^ d * (treeLenCovOne m₀ j X + 1) := by
  classical
  obtain ⟨𝒦, W, E, hch, hconn, hWX, hmeet, hcost⟩ := treeLenCovOne_attained m₀ j X hX
  set a := cellSide L m₀ m₁ j with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ j
  have hadvd : a ∣ (N₁ * L ^ m₁) * L ^ K := cellSide_dvd hN hj
  obtain ⟨m, hm⟩ := hadvd
  have hmne : NeZero m := ⟨fun h => by
    have : (N₁ * L ^ m₁) * L ^ K ≠ 0 := NeZero.ne _
    rw [hm, h] at this; simp at this⟩
  have hc1 := card_cells_le (d := d) hm ha0 hconn
  have hc2 := card_cbase_le (d := d) hm W
  have hc3 := cellCount_le (a := a) (X := X) (𝒦 := 𝒦) (W := W) ⟨m, hm⟩ ha0
    (fun b hb => (hch.1 b hb).1) hch.2 hmeet
  have hnat : a * cellCount a X ≤ L ^ d * L ^ d * (3 ^ d * (E.card + a)) := by
    calc a * cellCount a X ≤ a * (L ^ d * L ^ d * (W.image (cbase a)).card) :=
          Nat.mul_le_mul_left _ hc3
      _ = L ^ d * L ^ d * (a * (W.image (cbase a)).card) := by ring
      _ ≤ L ^ d * L ^ d * (a * (W.image (blockMap a m)).card) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc2)
      _ ≤ L ^ d * L ^ d * (3 ^ d * (E.card + a)) := Nat.mul_le_mul_left _ hc1
  have haR : (a : ℝ) = (L : ℝ) ^ (m₀ + m₁ + j) := by
    rw [ha]; unfold cellSide; push_cast; congr 1; ring
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha0
  have hcostE : treeLenCovOne m₀ j X = E.card / a := by
    rw [← hcost]; unfold bondCost scaleW
    rw [Finset.sum_const, nsmul_eq_mul, ← haR]; ring
  have hR : (a : ℝ) * cellCount a X ≤ (L : ℝ) ^ d * (L : ℝ) ^ d * (3 ^ d * (E.card + a)) := by
    exact_mod_cast hnat
  rw [hcostE, show (L : ℝ) ^ (2 * d) = (L : ℝ) ^ d * (L : ℝ) ^ d by ring]
  have e : (E.card : ℝ) / a + 1 = (E.card + a) / a := by field_simp
  rw [e, ← mul_div_assoc, le_div_iff₀ hapos]
  nlinarith [hR]

end SingleScale

end Balaban.Localization
