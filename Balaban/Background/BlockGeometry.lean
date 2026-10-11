/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Data
public import Balaban.Multiscale.PathMetricBounds
public import Balaban.Green.MassLipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Block geometry and separation consequences (LEMMA53-astra.md, §2 and §6, items 1-2)

The geometric inputs of the hard-spin approximate field of Lemma 5.3.  Everything is stated with
integer lifts of the torus coordinates:

* `torusDist_le_of_lift`: the torus distance is at most the `ℓ¹` distance of any two lifts;
* `mem_pred_of_dist_le`: a site within `4 d L ^ n` of `Ω_n` lies in `Ω_{n-1}` (separation);
* `layerIndex_le_succ_of_adj`, `layer_bounds_of_dist`: layers of nearby sites differ by at most one
  (Lemma 5.3a(1), (3));
* `chain_box`: the oscillation of a layer-constant function with bounded steps along the
  coordinate-monotone paths of a box of `Ω_{n-1}` is at most the number of cells of side
  `L ^ (n-1)` crossed (the replacement for the chain assertion of Lemma 5.3a(2)).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Distance

/-- The torus distance is at most the `ℓ¹` distance of any lifts of the two points. -/
theorem torusDist_le_of_lift {m : ℕ} [NeZero m] {x z : Torus d m} (t u : Fin d → ℤ)
    (ht : ∀ μ, ((t μ : ℤ) : ZMod m) = x μ) (hu : ∀ μ, ((u μ : ℤ) : ZMod m) = z μ) :
    Green.torusDist d m x z ≤ ∑ μ, ((t μ - u μ).natAbs : ℝ) := by
  unfold Green.torusDist
  refine Finset.sum_le_sum fun μ _ => ?_
  have := Green.natAbs_cycRep_le_of_cast (x μ - z μ) (t μ - u μ) (by push_cast; rw [ht, hu])
  exact_mod_cast this

/-- The lift of an arbitrary integer vector to the torus. -/
def castTorus {m : ℕ} (w : Fin d → ℤ) : Torus d m := fun μ => ((w μ : ℤ) : ZMod m)

theorem castTorus_apply {m : ℕ} (w : Fin d → ℤ) (μ : Fin d) :
    (castTorus w : Torus d m) μ = ((w μ : ℤ) : ZMod m) := rfl

theorem torusDist_castTorus_le {m : ℕ} [NeZero m] (w t : Fin d → ℤ) :
    Green.torusDist d m (castTorus w) (castTorus t) ≤ ∑ μ, ((w μ - t μ).natAbs : ℝ) :=
  torusDist_le_of_lift w t (fun _ => rfl) (fun _ => rfl)

end Distance

section Layers

variable (G : GeneratingSet d L N₀ k ϱ)

/-- `x ∈ Ω_j` iff `j ≤ layerIndex x`, for `x ∈ Ω₁`. -/
theorem mem_Ω_iff_le_layerIndex {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) {j : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k) : x ∈ G.Ω j ↔ j ≤ G.layerIndex x := by
  obtain ⟨h1, h2, hxl⟩ := G.layerIndex_spec hx
  rw [G.mem_layer] at hxl
  constructor
  · intro hj
    by_contra hlt
    replace hlt := not_le.1 hlt
    exact hxl.2 (G.Ω_antitone (by omega) (by omega) (by omega) hj)
  · intro hj
    exact G.Ω_antitone hj1 hj (by omega) hxl.1

theorem not_mem_Ω_layerIndex_succ {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    x ∉ G.Ω (G.layerIndex x + 1) :=
  (G.mem_layer.1 (G.layerIndex_spec hx).2.2).2

/-- Separation, contrapositive form: a site within `4 d L ^ n` of `Ω_n` lies in `Ω_{n-1}`. -/
theorem mem_pred_of_dist_le (hϱ : (4 * d * L : ℝ) ≤ ϱ) {n : ℕ} (hn1 : 2 ≤ n) (hnk : n ≤ k)
    {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω n)
    (h : Green.torusDist d (N₀ * L ^ k) x y ≤ 4 * d * (L : ℝ) ^ n) : y ∈ G.Ω (n - 1) := by
  by_contra hy
  have hn : n - 1 + 1 = n := by omega
  have hsep := G.separation (n - 1) (by omega) (by omega) y hy x (by rw [hn]; exact hx)
  rw [Green.torusDist_comm_gen] at hsep
  have hLn : (L : ℝ) ^ n = (L : ℝ) ^ (n - 1) * L := by
    rw [← pow_succ, hn]
  have hp : (0 : ℝ) ≤ (L : ℝ) ^ (n - 1) := by positivity
  have : (4 * d * L : ℝ) * (L : ℝ) ^ (n - 1) ≤ ϱ * (L : ℝ) ^ (n - 1) :=
    mul_le_mul_of_nonneg_right hϱ hp
  rw [hLn] at h
  nlinarith

/-- A neighbour of a site of `Ω_n`, `n ≥ 2`, lies in `Ω_{n-1}`. -/
theorem adj_mem_pred (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ} (hn1 : 2 ≤ n)
    (hnk : n ≤ k) {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω n) (h : Adj x x') :
    x' ∈ G.Ω (n - 1) := by
  refine mem_pred_of_dist_le G hϱ hn1 hnk hx (h.torusDist_le.trans ?_)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have : (1 : ℝ) ≤ (L : ℝ) ^ n := one_le_pow₀ hL'
  nlinarith

/-- Layers of adjacent sites of `Ω₁` differ by at most one. -/
theorem layerIndex_le_succ_of_adj (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hx' : x' ∈ G.Ω 1) (h : Adj x x') :
    G.layerIndex x ≤ G.layerIndex x' + 1 := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  obtain ⟨h1, h2, _⟩ := G.layerIndex_spec hx
  obtain ⟨h1', h2', _⟩ := G.layerIndex_spec hx'
  have hmem : x ∈ G.Ω (G.layerIndex x) := (mem_Ω_iff_le_layerIndex G hx h1 h2).2 le_rfl
  have := adj_mem_pred G hϱ hd hL (by omega) h2 hmem h
  have := (mem_Ω_iff_le_layerIndex G hx' (by omega) (by omega)).1 this
  omega

/-- Blocks lie in the layer of their base. -/
theorem mem_layer_of_mem_blk {m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k) {y z : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.layer m) (hz : z ∈ G.blk m y) : z ∈ G.layer m :=
  (G.mem_layer_iff hm1 hmk (G.mem_blk.1 hz)).2 hy

/-- Coarsening of cells. -/
theorem jBlock_mono {i j : ℕ} (hij : i ≤ j) (hjk : j ≤ k) {x x' : Torus d (N₀ * L ^ k)}
    (h : jBlock d L N₀ k i x = jBlock d L N₀ k i x') :
    jBlock d L N₀ k j x = jBlock d L N₀ k j x' := by
  induction j, hij using Nat.le_induction with
  | base => exact h
  | succ j hij ih => exact GeneratingSet.jBlock_succ_eq (by omega) (ih (by omega))

/-- Two sites of `Ω_i` in the same `i`-cell have the same layer. -/
theorem layerIndex_eq_of_cell_eq {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) {y y' : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.Ω i) (h : jBlock d L N₀ k i y = jBlock d L N₀ k i y') :
    G.layerIndex y = G.layerIndex y' := by
  have hy1 : y ∈ G.Ω 1 := G.Ω_antitone le_rfl hi1 (by omega) hy
  obtain ⟨h1, h2, hyl⟩ := G.layerIndex_spec hy1
  have hge := (mem_Ω_iff_le_layerIndex G hy1 hi1 hik).1 hy
  have hh := jBlock_mono hge h2 h
  have hy'l : y' ∈ G.layer (G.layerIndex y) := (G.mem_layer_iff h1 h2 hh).1 hyl
  exact (G.layerIndex_eq h1 h2 hy'l).symm

/-- Lemma 5.3a(1),(3): if a site of layer `n` is within `4 d L ^ m` of a site of layer `m`, then
`|m - n| ≤ 1`. -/
theorem layer_bounds_of_dist (hϱ : (4 * d * L : ℝ) ≤ ϱ) {m n : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k)
    (hn1 : 1 ≤ n) (hnk : n ≤ k) {x z : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n)
    (hz : z ∈ G.layer m)
    (h : Green.torusDist d (N₀ * L ^ k) x z ≤ 4 * d * (L : ℝ) ^ m) (hL : 1 ≤ L) :
    n ≤ m + 1 ∧ m ≤ n + 1 := by
  rw [G.mem_layer] at hx hz
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  constructor
  · by_contra hlt
    replace hlt := not_le.1 hlt
    have := mem_pred_of_dist_le G hϱ (by omega) hnk hx.1
      (h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL' (by omega)) (by positivity)))
    exact hz.2 (G.Ω_antitone (by omega) (by omega) (by omega) this)
  · by_contra hlt
    replace hlt := not_le.1 hlt
    rw [Green.torusDist_comm_gen] at h
    have := mem_pred_of_dist_le G hϱ (by omega) hmk hz.1 h
    exact hx.2 (G.Ω_antitone (by omega) (by omega) (by omega) this)

end Layers

section Chain

/-- The cell of an integer coordinate at scale `lam` is its floor quotient. -/
theorem blockCoord_intCast {S m lam : ℕ} [NeZero S] [NeZero m] (hS : S = lam * m) (hlam : 0 < lam)
    (t : ℤ) : Balaban.blockCoord lam m ((t : ZMod S)) = (((t / (lam : ℤ) : ℤ)) : ZMod m) := by
  unfold Balaban.blockCoord
  have hv : (((t : ZMod S).val : ℕ) : ℤ) = t % (S : ℤ) := ZMod.val_intCast t
  obtain ⟨r, q, hr, ht⟩ : ∃ r q : ℤ, r = (((t : ZMod S).val : ℕ) : ℤ) ∧
      t = r + (lam : ℤ) * ((m : ℤ) * q) := by
    refine ⟨_, t / (S : ℤ), rfl, ?_⟩
    have := Int.emod_add_mul_ediv t (S : ℤ)
    rw [← hv] at this
    rw [hS] at this ⊢
    push_cast at this ⊢
    linarith
  have hl : (lam : ℤ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hdiv : t / (lam : ℤ) = r / (lam : ℤ) + (m : ℤ) * q := by
    conv_lhs => rw [ht]
    rw [Int.add_mul_ediv_left r _ hl]
  rw [hdiv]
  have : (((t : ZMod S).val / lam : ℕ) : ZMod m) = ((r / (lam : ℤ) : ℤ) : ZMod m) := by
    rw [hr]
    have : ((((t : ZMod S).val / lam : ℕ) : ℤ)) = (((t : ZMod S).val : ℕ) : ℤ) / (lam : ℤ) := by
      push_cast; rfl
    rw [← Int.cast_natCast, this]
  rw [this]
  push_cast
  simp

theorem jBlock_castTorus_eq {j : ℕ} (hjk : j ≤ k) (w w' : Fin d → ℤ)
    (h : ∀ μ, w μ / ((L ^ j : ℕ) : ℤ) = w' μ / ((L ^ j : ℕ) : ℤ)) :
    jBlock d L N₀ k j (castTorus w) = jBlock d L N₀ k j (castTorus w') := by
  have hLj : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  funext μ
  unfold jBlock
  rw [Balaban.blockMap_apply, Balaban.blockMap_apply, castTorus_apply, castTorus_apply,
    blockCoord_intCast (side_eq hjk) hLj, blockCoord_intCast (side_eq hjk) hLj, h μ]

variable {V : Type*} [SeminormedAddCommGroup V]

theorem line_bound (lam : ℤ) (hlam : 0 < lam) (g : ℤ → V) (E : ℝ) (hE : 0 ≤ E) (a b : ℤ)
    (hab : a ≤ b) (hstep : ∀ i, a ≤ i → i < b → ‖g (i + 1) - g i‖ ≤ E)
    (hcell : ∀ i, a ≤ i → i < b → i / lam = (i + 1) / lam → g (i + 1) = g i) :
    ‖g b - g a‖ ≤ E * ((b / lam - a / lam : ℤ) : ℝ) := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hab ih =>
    have ih := ih (fun i h1 h2 => hstep i h1 (by omega)) (fun i h1 h2 => hcell i h1 (by omega))
    have h1 : ‖g (b + 1) - g b‖ ≤ E * (((b + 1) / lam - b / lam : ℤ) : ℝ) := by
      by_cases hc : b / lam = (b + 1) / lam
      · rw [hcell b hab (by omega) hc]
        simp [hc]
      · have hlt : b / lam < (b + 1) / lam :=
          lt_of_le_of_ne (Int.ediv_le_ediv hlam (by omega)) hc
        calc ‖g (b + 1) - g b‖ ≤ E := hstep b hab (by omega)
          _ ≤ E * (((b + 1) / lam - b / lam : ℤ) : ℝ) :=
            le_mul_of_one_le_right hE (by exact_mod_cast (by omega : (1 : ℤ) ≤ (b + 1) / lam - b / lam))
    calc ‖g (b + 1) - g a‖ = ‖(g (b + 1) - g b) + (g b - g a)‖ := by congr 1; abel
      _ ≤ ‖g (b + 1) - g b‖ + ‖g b - g a‖ := norm_add_le _ _
      _ ≤ E * (((b + 1) / lam - b / lam : ℤ) : ℝ) + E * ((b / lam - a / lam : ℤ) : ℝ) :=
          add_le_add h1 ih
      _ = E * (((b + 1) / lam - a / lam : ℤ) : ℝ) := by push_cast; ring

/-- Number of cells crossed. -/
theorem cells_crossed_le (lam : ℕ) (hlam : 0 < lam) (a b : ℤ) :
    ((b / (lam : ℤ) - a / (lam : ℤ) : ℤ) : ℝ) ≤ ((b - a : ℤ) : ℝ) / lam + 1 := by
  have hl : (0 : ℤ) < lam := by exact_mod_cast hlam
  have h1 := Int.ediv_mul_le b hl.ne'
  have h2 := Int.lt_ediv_add_one_mul_self a hl
  have hlR : (0 : ℝ) < lam := by exact_mod_cast hlam
  have h1' : ((b / (lam : ℤ) * lam : ℤ) : ℝ) ≤ b := by exact_mod_cast h1
  have h2' : (a : ℝ) < (((a / (lam : ℤ) + 1) * lam : ℤ) : ℝ) := by exact_mod_cast h2
  push_cast at h1' h2' ⊢
  have e : ((b : ℝ) - a) / lam + 1 = ((b - a) + lam) / lam := by field_simp
  rw [e, le_div_iff₀ hlR]
  nlinarith


/-- Symmetric form of `line_bound`: the number of cells crossed is at most `|a - b| / lam + 1`. -/
theorem line_bound_sym (lam : ℕ) (hlam : 0 < lam) (g : ℤ → V) (E : ℝ) (hE : 0 ≤ E) (a b : ℤ)
    (hstep : ∀ i, min a b ≤ i → i < max a b → ‖g (i + 1) - g i‖ ≤ E)
    (hcell : ∀ i, min a b ≤ i → i < max a b → i / (lam : ℤ) = (i + 1) / (lam : ℤ) →
      g (i + 1) = g i) :
    ‖g b - g a‖ ≤ E * (((a - b).natAbs : ℝ) / lam + 1) := by
  have hl : (0 : ℤ) < lam := by exact_mod_cast hlam
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab] at hstep hcell
    refine (line_bound (lam : ℤ) hl g E hE a b hab hstep hcell).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hE
    refine (cells_crossed_le lam hlam a b).trans ?_
    have : ((b - a : ℤ) : ℝ) = (((a - b).natAbs : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs]; push_cast
      rw [abs_of_nonpos (by linarith [(by exact_mod_cast hab : (a : ℝ) ≤ b)])]; ring
    rw [this]
  · rw [min_eq_right hab, max_eq_left hab] at hstep hcell
    have := line_bound (lam : ℤ) hl g E hE b a hab hstep hcell
    rw [norm_sub_rev]
    refine this.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hE
    refine (cells_crossed_le lam hlam b a).trans ?_
    have : ((a - b : ℤ) : ℝ) = (((a - b).natAbs : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs]; push_cast
      rw [abs_of_nonneg (by linarith [(by exact_mod_cast hab : (b : ℝ) ≤ a)])]
    rw [this]


/-- **The chain estimate** (replacement for Lemma 5.3a(2)).  Let `f` change by at most `E` across
every bond of `Ω_{n-1}` and be constant on the cells of side `L ^ (n-1)` inside `Ω_{n-1}`.
If the box spanned by the lifts `t`, `u` lies in `Ω_{n-1}`, then `f` at the two corners differs by at
most `E` times the number of cells of side `L ^ (n-1)` crossed along a coordinatewise path. -/
theorem chain_box (G : GeneratingSet d L N₀ k ϱ) (f : Torus d (N₀ * L ^ k) → V) (E : ℝ)
    (hE : 0 ≤ E) {n : ℕ} (hn1 : 2 ≤ n) (hnk : n ≤ k)
    (hstep : ∀ y y', y ∈ G.Ω (n - 1) → y' ∈ G.Ω (n - 1) → Adj y y' → ‖f y' - f y‖ ≤ E)
    (hcell : ∀ y y', y ∈ G.Ω (n - 1) → y' ∈ G.Ω (n - 1) →
      jBlock d L N₀ k (n - 1) y = jBlock d L N₀ k (n - 1) y' → f y' = f y)
    (t u : Fin d → ℤ)
    (hbox : ∀ w : Fin d → ℤ, (∀ μ, min (t μ) (u μ) ≤ w μ ∧ w μ ≤ max (t μ) (u μ)) →
      (castTorus w : Torus d (N₀ * L ^ k)) ∈ G.Ω (n - 1)) :
    ‖f (castTorus u) - f (castTorus t)‖ ≤
      E * ∑ μ, (((t μ - u μ).natAbs : ℝ) / (L : ℝ) ^ (n - 1) + 1) := by
  classical
  have hLpos : 0 < L ^ (n - 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  set W : Finset (Fin d) → Fin d → ℤ := fun s μ => if μ ∈ s then u μ else t μ with hW
  have key : ∀ s : Finset (Fin d), ‖f (castTorus (W s)) - f (castTorus t)‖ ≤
      E * ∑ μ ∈ s, (((t μ - u μ).natAbs : ℝ) / (L : ℝ) ^ (n - 1) + 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : W ∅ = t := by funext μ; simp [hW]
      rw [this]; simp
    | insert μ s hμ ih =>
      have hWs : W (insert μ s) = Function.update (W s) μ (u μ) := by
        funext ν
        by_cases h : ν = μ
        · subst h; simp [hW]
        · simp [hW, h]
      have hWs' : W s = Function.update (W s) μ (t μ) := by
        funext ν
        by_cases h : ν = μ
        · subst h; simp [hW, hμ]
        · simp [h]
      set g : ℤ → V := fun i => f (castTorus (Function.update (W s) μ i)) with hg
      have hbox' : ∀ i, min (t μ) (u μ) ≤ i → i ≤ max (t μ) (u μ) →
          (castTorus (Function.update (W s) μ i) : Torus d (N₀ * L ^ k)) ∈ G.Ω (n - 1) := by
        intro i h1 h2
        refine hbox _ fun ν => ?_
        by_cases h : ν = μ
        · subst h; simp only [Function.update_self]; exact ⟨h1, h2⟩
        · simp only [Function.update_of_ne h, hW]
          split_ifs
          · exact ⟨min_le_right _ _, le_max_right _ _⟩
          · exact ⟨min_le_left _ _, le_max_left _ _⟩
      have hline := line_bound_sym (L ^ (n - 1)) hLpos g (E) hE (t μ) (u μ)
        (fun i h1 h2 => by
          refine hstep _ _ (hbox' i h1 h2.le) (hbox' (i + 1) (by omega) (by omega)) ⟨μ, Or.inl ?_⟩
          funext ν
          by_cases h : ν = μ
          · subst h; simp [castTorus]
          · simp [castTorus, Function.update_of_ne h, Pi.single_eq_of_ne h])
        (fun i h1 h2 hc => by
          refine hcell _ _ (hbox' i h1 h2.le) (hbox' (i + 1) (by omega) (by omega)) ?_
          refine jBlock_castTorus_eq (by omega) _ _ fun ν => ?_
          by_cases h : ν = μ
          · subst h; simpa using hc
          · simp [Function.update_of_ne h])
      have h1 : g (u μ) = f (castTorus (W (insert μ s))) := by rw [hWs]
      have h2 : g (t μ) = f (castTorus (W s)) := by
        simp only [hg]; rw [← hWs']
      rw [h1, h2] at hline
      rw [Finset.sum_insert hμ, mul_add]
      calc ‖f (castTorus (W (insert μ s))) - f (castTorus t)‖
          ≤ ‖f (castTorus (W (insert μ s))) - f (castTorus (W s))‖ +
            ‖f (castTorus (W s)) - f (castTorus t)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := by
          refine add_le_add ?_ ih
          convert hline using 3
          push_cast; ring
  have := key Finset.univ
  have hu : W Finset.univ = u := by funext μ; simp [hW]
  rwa [hu] at this


/-- The box spanned by two lifts at `ℓ¹` distance at most `4 d L ^ n` from a point of `Ω_n` lies in
`Ω_{n-1}`. -/
theorem box_mem_pred (G : GeneratingSet d L N₀ k ϱ) (hϱ : (4 * d * L : ℝ) ≤ ϱ) {n : ℕ}
    (hn1 : 2 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω n)
    (t u : Fin d → ℤ) (htx : ∀ μ, ((t μ : ℤ) : ZMod (N₀ * L ^ k)) = x μ)
    (hdist : ∑ μ, ((t μ - u μ).natAbs : ℝ) ≤ 4 * d * (L : ℝ) ^ n) (w : Fin d → ℤ)
    (hw : ∀ μ, min (t μ) (u μ) ≤ w μ ∧ w μ ≤ max (t μ) (u μ)) :
    (castTorus w : Torus d (N₀ * L ^ k)) ∈ G.Ω (n - 1) := by
  refine mem_pred_of_dist_le G hϱ hn1 hnk hx ((torusDist_le_of_lift t w htx (fun _ => rfl)).trans
    (le_trans (Finset.sum_le_sum fun μ _ => ?_) hdist))
  have := hw μ
  have h1 : (t μ - w μ).natAbs ≤ (t μ - u μ).natAbs := by
    rcases le_total (t μ) (u μ) with h | h
    · rw [min_eq_left h, max_eq_right h] at this; omega
    · rw [min_eq_right h, max_eq_left h] at this; omega
  exact_mod_cast h1

/-- **Chain to an active block.**  `x` of layer `n ≥ 2`, `z` of layer `m` (`|m - n| ≤ 1`) with lifts
within `L ^ m` in each coordinate; `f` as in `chain_box`. -/
theorem chain_to_block (G : GeneratingSet d L N₀ k ϱ) (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d)
    (hL : 1 ≤ L) (f : Torus d (N₀ * L ^ k) → V) (E : ℝ) (hE : 0 ≤ E) {n m : ℕ} (hn1 : 2 ≤ n)
    (hnk : n ≤ k) (hmk : m ≤ k) (hnm : m ≤ n + 1) (hmn : n ≤ m + 1)
    (hstep : ∀ y y', y ∈ G.Ω (n - 1) → y' ∈ G.Ω (n - 1) → Adj y y' → ‖f y' - f y‖ ≤ E)
    (hcell : ∀ y y', y ∈ G.Ω (n - 1) → y' ∈ G.Ω (n - 1) →
      jBlock d L N₀ k (n - 1) y = jBlock d L N₀ k (n - 1) y' → f y' = f y)
    {x z : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω n) (hz : z ∈ G.Ω m) (t u : Fin d → ℤ)
    (htx : ∀ μ, ((t μ : ℤ) : ZMod (N₀ * L ^ k)) = x μ)
    (huz : ∀ μ, ((u μ : ℤ) : ZMod (N₀ * L ^ k)) = z μ)
    (hlift : ∀ μ, (t μ - u μ).natAbs ≤ L ^ m) :
    ‖f z - f x‖ ≤ E * (d * ((L : ℝ) ^ 2 + 1)) := by
  have hx' : x = castTorus t := funext fun μ => (htx μ).symm
  have hz' : z = castTorus u := funext fun μ => (huz μ).symm
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hsum : ∑ μ, ((t μ - u μ).natAbs : ℝ) ≤ d * (L : ℝ) ^ m := by
    calc ∑ μ, ((t μ - u μ).natAbs : ℝ) ≤ ∑ _μ : Fin d, (L : ℝ) ^ m :=
          Finset.sum_le_sum fun μ _ => by exact_mod_cast hlift μ
      _ = d * (L : ℝ) ^ m := by simp
  have hLm : (0 : ℝ) ≤ (L : ℝ) ^ m := by positivity
  have hd' : (0 : ℝ) ≤ d := by positivity
  have hbox : ∀ w : Fin d → ℤ, (∀ μ, min (t μ) (u μ) ≤ w μ ∧ w μ ≤ max (t μ) (u μ)) →
      (castTorus w : Torus d (N₀ * L ^ k)) ∈ G.Ω (n - 1) := by
    intro w hw
    by_cases hmn' : m ≤ n
    · refine box_mem_pred G hϱ hn1 hnk hx t u htx ?_ w hw
      calc ∑ μ, ((t μ - u μ).natAbs : ℝ) ≤ d * (L : ℝ) ^ m := hsum
        _ ≤ d * (L : ℝ) ^ n := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL' hmn') hd'
        _ ≤ 4 * d * (L : ℝ) ^ n := by nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ L) n]
    · have hm : m = n + 1 := by omega
      subst hm
      have h := box_mem_pred G hϱ (n := n + 1) (by omega) hmk hz u t huz
        (by
          calc ∑ μ, ((u μ - t μ).natAbs : ℝ) = ∑ μ, ((t μ - u μ).natAbs : ℝ) :=
                Finset.sum_congr rfl fun μ _ => by rw [← Int.natAbs_neg, neg_sub]
            _ ≤ d * (L : ℝ) ^ (n + 1) := hsum
            _ ≤ 4 * d * (L : ℝ) ^ (n + 1) := by nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ L) (n + 1)])
        w (fun μ => by rw [min_comm, max_comm]; exact hw μ)
      have : n + 1 - 1 = n := by omega
      rw [this] at h
      exact G.Ω_antitone (by omega) (by omega) (by omega) h
  have := chain_box G f E hE hn1 hnk hstep hcell t u hbox
  rw [hx', hz']
  refine this.trans (mul_le_mul_of_nonneg_left ?_ hE)
  calc ∑ μ, (((t μ - u μ).natAbs : ℝ) / (L : ℝ) ^ (n - 1) + 1)
      ≤ ∑ _μ : Fin d, ((L : ℝ) ^ 2 + 1) := by
        refine Finset.sum_le_sum fun μ _ => ?_
        have hp : (0 : ℝ) < (L : ℝ) ^ (n - 1) := by positivity
        have h1 : ((t μ - u μ).natAbs : ℝ) ≤ (L : ℝ) ^ m := by exact_mod_cast hlift μ
        have h2 : (L : ℝ) ^ m ≤ (L : ℝ) ^ (n - 1) * (L : ℝ) ^ 2 := by
          rw [← pow_add]; exact pow_le_pow_right₀ hL' (by omega)
        have : ((t μ - u μ).natAbs : ℝ) / (L : ℝ) ^ (n - 1) ≤ (L : ℝ) ^ 2 := by
          rw [div_le_iff₀ hp]; nlinarith
        linarith
    _ = d * ((L : ℝ) ^ 2 + 1) := by simp; ring

end Chain

end Balaban.Background
