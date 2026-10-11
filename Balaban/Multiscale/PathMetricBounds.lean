/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PathMetric
public import Balaban.Multiscale.Coercivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lipschitz and block bounds for the multiscale path metric (GREEN.md §4.2, Lemma 4.3 (b), (c))

For the path metric `Balaban.Multiscale.GeneratingSet.pathDist` of
`Balaban/Multiscale/PathMetric.lean` (fine unit spacing):

* `Balaban.Multiscale.GeneratingSet.distTo y' x`: the real distance `(d(x, y')).toReal` (it is `0`
  when `d = ⊤`, which happens only when `x` and `y'` are not joined by a path inside `Ω₁`);
* `distTo_lipschitz` (Lemma 4.3 (c)): for adjacent `x, x' ∈ Ω₁`,
  `|distTo y' x - distTo y' x'| ≤ 1 / ℓ(b)`, in particular `≤ 1 / ℓ(x)` and `≤ 1`;
* `pathDist_block_le` (Lemma 4.3 (b)): two points of one `j`-block of layer `j` have
  `d(x, x') ≤ 2 d`, and `distTo_block` is the corresponding Lipschitz bound.

The source states `d(x, x') ≤ d` for (b); the path used here goes from each of the two points down to
the corner of the block, so the constant is `2 d`.
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-! ### From one-sided triangle inequalities to a real Lipschitz bound -/

theorem abs_toReal_sub_le {a b : ENNReal} {c : ℝ} (hc : 0 ≤ c) (hab : a ≤ ENNReal.ofReal c + b)
    (hba : b ≤ ENNReal.ofReal c + a) : |a.toReal - b.toReal| ≤ c := by
  by_cases ha : a = ⊤
  · have hb : b = ⊤ := by
      by_contra hb
      rw [ha] at hab
      exact absurd (top_le_iff.1 hab) (by simp [ENNReal.add_eq_top, hb])
    simp [ha, hb, hc]
  · by_cases hb : b = ⊤
    · exfalso
      rw [hb] at hba
      exact absurd (top_le_iff.1 hba) (by simp [ENNReal.add_eq_top, ha])
    · have h1 : a.toReal ≤ c + b.toReal := by
        have := ENNReal.toReal_mono (by simp [ENNReal.add_eq_top, hb]) hab
        rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top hb, ENNReal.toReal_ofReal hc] at this
      have h2 : b.toReal ≤ c + a.toReal := by
        have := ENNReal.toReal_mono (by simp [ENNReal.add_eq_top, ha]) hba
        rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top ha, ENNReal.toReal_ofReal hc] at this
      rw [abs_le]
      constructor <;> linarith

/-! ### Adjacency and the torus distance -/

section Adjacent

omit [NeZero N₀] [NeZero L] in
theorem torusDist_comm' (x y : Torus d (N₀ * L ^ k)) [NeZero (N₀ * L ^ k)] :
    Green.torusDist d (N₀ * L ^ k) x y = Green.torusDist d (N₀ * L ^ k) y x := by
  unfold Green.torusDist
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Green.natAbs_cycRep_neg (x i - y i), neg_sub]

theorem torusDist_triangle' (x y z : Torus d (N₀ * L ^ k)) :
    Green.torusDist d (N₀ * L ^ k) x z ≤
      Green.torusDist d (N₀ * L ^ k) x y + Green.torusDist d (N₀ * L ^ k) y z := by
  have := dist_triangle (show Green.L1Torus d (N₀ * L ^ k) from x) y z
  exact this

theorem torusDist_self' (x : Torus d (N₀ * L ^ k)) : Green.torusDist d (N₀ * L ^ k) x x = 0 := by
  have := dist_self (show Green.L1Torus d (N₀ * L ^ k) from x)
  exact this

omit [NeZero N₀] [NeZero L] in
theorem torusDist_nonneg' (x y : Torus d (N₀ * L ^ k)) : 0 ≤ Green.torusDist d (N₀ * L ^ k) x y :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem torusDist_add_single_le (x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    Green.torusDist d (N₀ * L ^ k) x (x + Pi.single μ 1) ≤ 1 := by
  unfold Green.torusDist
  rw [Finset.sum_eq_single μ]
  · simp only [Pi.add_apply, Pi.single_eq_same, sub_add_cancel_left]
    have := Green.natAbs_cycRep_le_of_cast (m := N₀ * L ^ k) (-1 : ZMod (N₀ * L ^ k)) (-1)
      (by simp)
    exact_mod_cast this
  · intro i _ hi
    simp [hi, Green.natAbs_cycRep_zero]
  · simp

theorem Adj.torusDist_le {x y : Torus d (N₀ * L ^ k)} (h : Adj x y) :
    Green.torusDist d (N₀ * L ^ k) x y ≤ 1 := by
  obtain ⟨μ, h | h⟩ := h
  · rw [h]; exact torusDist_add_single_le x μ
  · rw [h, torusDist_comm']; exact torusDist_add_single_le y μ

end Adjacent

namespace GeneratingSet

variable (G : GeneratingSet d L N₀ k ϱ)

theorem spacing_ge_one (x : Torus d (N₀ * L ^ k)) : 1 ≤ G.spacing x := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  exact one_le_pow₀ hL

theorem bondCost_le_inv_left (x y : Torus d (N₀ * L ^ k)) : G.bondCost x y ≤ 1 / G.spacing x := by
  unfold bondCost
  exact one_div_le_one_div_of_le (lt_of_lt_of_le one_pos (G.spacing_ge_one x)) (le_max_left _ _)

theorem bondCost_le_inv_right (x y : Torus d (N₀ * L ^ k)) : G.bondCost x y ≤ 1 / G.spacing y := by
  rw [bondCost_comm]; exact G.bondCost_le_inv_left y x

/-! ### The real distance and Lemma 4.3 (c) -/

/-- The real distance `d(x, y')` of (1.9) (`0` when `d(x, y') = ⊤`). -/
noncomputable def distTo (y' x : Torus d (N₀ * L ^ k)) : ℝ := (G.pathDist x y').toReal

theorem distTo_nonneg (y' x : Torus d (N₀ * L ^ k)) : 0 ≤ G.distTo y' x := ENNReal.toReal_nonneg

/-- **Lemma 4.3 (c).** `|d(x, y') - d(x', y')| ≤ 1 / ℓ(b)` for a bond `b = (x, x')` of `Ω₁`. -/
theorem distTo_lipschitz (y' : Torus d (N₀ * L ^ k)) {x x' : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (hx' : x' ∈ G.Ω 1) (hadj : Adj x x') :
    |G.distTo y' x - G.distTo y' x'| ≤ G.bondCost x x' := by
  refine abs_toReal_sub_le (G.bondCost_nonneg x x') ?_ ?_
  · exact (G.pathDist_triangle x x' y').trans (by gcongr; exact G.pathDist_le_bondCost hx hx' hadj)
  · refine (G.pathDist_triangle x' x y').trans (by
      gcongr
      rw [bondCost_comm]; exact G.pathDist_le_bondCost hx' hx hadj.symm)

theorem distTo_lipschitz_le_one (y' : Torus d (N₀ * L ^ k)) {x x' : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (hx' : x' ∈ G.Ω 1) (hadj : Adj x x') :
    |G.distTo y' x - G.distTo y' x'| ≤ 1 / G.spacing x :=
  (G.distTo_lipschitz y' hx hx' hadj).trans (G.bondCost_le_inv_left x x')

/-! ### Lower bounds for the path metric by Lipschitz functions -/

theorem sub_le_of_pathCost (F : Torus d (N₀ * L ^ k) → ℝ)
    (hF : ∀ x x', x ∈ G.Ω 1 → x' ∈ G.Ω 1 → Adj x x' → |F x - F x'| ≤ G.bondCost x x')
    {x y : Torus d (N₀ * L ^ k)} {c : ℝ} (h : G.PathCost x y c) : F y - F x ≤ c := by
  induction h with
  | refl x hx => simp
  | step x y z c hx hadj hp ih =>
      have h1 := hF x y hx hp.left_mem hadj
      have h2 := neg_abs_le (F x - F y)
      linarith

/-- A function that is `1 / ℓ(b)`-Lipschitz along bonds of `Ω₁` is dominated by the path metric. -/
theorem ofReal_sub_le_pathDist (F : Torus d (N₀ * L ^ k) → ℝ)
    (hF : ∀ x x', x ∈ G.Ω 1 → x' ∈ G.Ω 1 → Adj x x' → |F x - F x'| ≤ G.bondCost x x')
    (x y : Torus d (N₀ * L ^ k)) : ENNReal.ofReal (F y - F x) ≤ G.pathDist x y := by
  refine le_iInf₂ fun c hc => ?_
  exact ENNReal.ofReal_le_ofReal (G.sub_le_of_pathCost F hF hc)

/-! ### Lemma 4.3 (b): distance inside a block -/

theorem mod_pred {v N : ℕ} (hN : 0 < N) (h : 0 < v % N) : (v - 1) % N = v % N - 1 := by
  have h1 := Nat.div_add_mod v N
  have h2 := Nat.mod_lt v hN
  have : v - 1 = N * (v / N) + (v % N - 1) := by omega
  rw [this, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem exists_corner {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∀ n : ℕ, ∀ x : Torus d (N₀ * L ^ k), x ∈ G.layer j → ∑ μ, (x μ).val % L ^ j = n →
      ∃ c : Torus d (N₀ * L ^ k), (∀ μ, (c μ).val % L ^ j = 0) ∧
        jBlock d L N₀ k j c = jBlock d L N₀ k j x ∧ G.PathCost x c ((n : ℝ) / (L : ℝ) ^ j) := by
  intro n
  induction n with
  | zero =>
      intro x hx hs
      refine ⟨x, fun μ => ?_, rfl, ?_⟩
      · exact (Finset.sum_eq_zero_iff.1 hs) μ (mem_univ μ)
      · simpa using PathCost.refl x (G.layer_subset hj hjk hx)
  | succ n ih =>
      intro x hx hs
      obtain ⟨μ, -, hμ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := univ)
        (f := fun μ => (x μ).val % L ^ j) (by rw [hs]; omega)
      have hpos : 0 < (x μ).val % L ^ j := Nat.pos_of_ne_zero hμ
      have hNpos : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero j (NeZero.ne L))
      set N := L ^ j with hN
      set x₁ : Torus d (N₀ * L ^ k) := x - Pi.single μ 1 with hx₁
      have hxx₁ : x = x₁ + Pi.single μ 1 := by rw [hx₁]; abel
      have hvpos : 0 < (x μ).val := by
        by_contra h0
        have : (x μ).val = 0 := by omega
        rw [this] at hpos; simp at hpos
      have hℓ2 : 1 < N₀ * L ^ k := by
        have := ZMod.val_lt (x μ)
        omega
      have hone : (1 : ZMod (N₀ * L ^ k)).val = 1 := by
        rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hℓ2]
      have hv1 : (x₁ μ).val = (x μ).val - 1 := by
        have : x₁ μ = x μ - 1 := by simp [hx₁]
        rw [this, ZMod.val_sub (by rw [hone]; omega), hone]
      have hother : ∀ ν, ν ≠ μ → x₁ ν = x ν := by
        intro ν hν; simp [hx₁, hν]
      have hrem1 : (x₁ μ).val % N = (x μ).val % N - 1 := by
        rw [hv1]; exact mod_pred hNpos hpos
      have hsum : ∑ ν, (x₁ ν).val % N = n := by
        have e1 : ∑ ν, (x ν).val % N = ((x μ).val % N) + ∑ ν ∈ univ.erase μ, (x ν).val % N :=
          (Finset.add_sum_erase _ _ (mem_univ μ)).symm
        have e2 : ∑ ν, (x₁ ν).val % N = ((x₁ μ).val % N) + ∑ ν ∈ univ.erase μ, (x₁ ν).val % N :=
          (Finset.add_sum_erase _ _ (mem_univ μ)).symm
        have e3 : ∑ ν ∈ univ.erase μ, (x₁ ν).val % N = ∑ ν ∈ univ.erase μ, (x ν).val % N :=
          Finset.sum_congr rfl fun ν hν => by rw [hother ν (Finset.ne_of_mem_erase hν)]
        omega
      have hlt : (x₁ μ).val % N + 1 < N := by
        have := Nat.mod_lt (x μ).val hNpos
        omega
      have hblock : jBlock d L N₀ k j x = jBlock d L N₀ k j x₁ := by
        unfold jBlock
        conv_lhs => rw [hxx₁]
        exact blockMap_add_single_of_inner (side_eq hjk) hlt
      have hx₁l : x₁ ∈ G.layer j := (G.mem_layer_iff hj hjk hblock).1 hx
      obtain ⟨c, hc0, hcb, hcp⟩ := ih x₁ hx₁l hsum
      refine ⟨c, hc0, hcb.trans hblock.symm, ?_⟩
      have hadj : Adj x x₁ := ⟨μ, Or.inr hxx₁⟩
      have hbc : G.bondCost x x₁ = 1 / (L : ℝ) ^ j := by
        unfold bondCost
        rw [G.spacing_eq hj hjk hx, G.spacing_eq hj hjk hx₁l, max_self]
      refine (PathCost.step x x₁ c _ (G.layer_subset hj hjk hx) hadj hcp).congr_cost ?_
      rw [hbc]
      push_cast
      ring

theorem pathCost_corner_le {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer j) :
    ∃ c : Torus d (N₀ * L ^ k), (∀ μ, (c μ).val % L ^ j = 0) ∧
      jBlock d L N₀ k j c = jBlock d L N₀ k j x ∧ ∃ t : ℝ, t ≤ d ∧ G.PathCost x c t := by
  obtain ⟨c, h1, h2, h3⟩ := G.exists_corner hj hjk _ x hx rfl
  refine ⟨c, h1, h2, _, ?_, h3⟩
  have hN : (0 : ℝ) < (L : ℝ) ^ j := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [div_le_iff₀ hN]
  have : ∑ μ, (x μ).val % L ^ j ≤ ∑ _μ : Fin d, L ^ j :=
    Finset.sum_le_sum fun μ _ => (Nat.mod_lt _ (by
      have := Nat.pos_of_ne_zero (pow_ne_zero j (NeZero.ne L)); exact this)).le
  have h4 : ((∑ μ, (x μ).val % L ^ j : ℕ) : ℝ) ≤ ((∑ _μ : Fin d, L ^ j : ℕ) : ℝ) :=
    Nat.cast_le.2 this
  simpa [mul_comm] using h4

theorem corner_eq {j : ℕ} (hjk : j ≤ k) {c c' : Torus d (N₀ * L ^ k)}
    (hc : ∀ μ, (c μ).val % L ^ j = 0) (hc' : ∀ μ, (c' μ).val % L ^ j = 0)
    (h : jBlock d L N₀ k j c = jBlock d L N₀ k j c') : c = c' := by
  funext μ
  have hμ := congrFun h μ
  unfold jBlock at hμ
  rw [blockMap_apply, blockMap_apply] at hμ
  have hv := congrArg ZMod.val hμ
  rw [blockCoord_val (side_eq hjk), blockCoord_val (side_eq hjk)] at hv
  apply ZMod.val_injective
  have e1 := Nat.div_add_mod (c μ).val (L ^ j)
  have e2 := Nat.div_add_mod (c' μ).val (L ^ j)
  rw [hc μ] at e1
  rw [hc' μ] at e2
  rw [hv] at e1
  omega

/-- **Lemma 4.3 (b).** Two points of one `j`-block of layer `j` are at distance `≤ 2 d`
(through the corner of the block; the source's constant is `d`). -/
theorem pathDist_block_le {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {x x' : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer j) (h : jBlock d L N₀ k j x' = jBlock d L N₀ k j x) :
    G.pathDist x x' ≤ ENNReal.ofReal (2 * d) := by
  have hx' : x' ∈ G.layer j := (G.mem_layer_iff hj hjk h).2 hx
  obtain ⟨c, hc, hcb, t, ht, hp⟩ := G.pathCost_corner_le hj hjk hx
  obtain ⟨c', hc', hcb', t', ht', hp'⟩ := G.pathCost_corner_le hj hjk hx'
  have hcc : c = c' := corner_eq hjk hc hc' (hcb.trans (h.symm.trans hcb'.symm))
  subst hcc
  refine (pathDist_le (hp.trans hp'.symm)).trans (ENNReal.ofReal_le_ofReal ?_)
  linarith

theorem distTo_block (y' : Torus d (N₀ * L ^ k)) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j)
    (h : jBlock d L N₀ k j x' = jBlock d L N₀ k j x) :
    |G.distTo y' x - G.distTo y' x'| ≤ 2 * d := by
  have hd : (0 : ℝ) ≤ 2 * d := by positivity
  have h1 := G.pathDist_block_le hj hjk hx h
  have h2 : G.pathDist x' x ≤ ENNReal.ofReal (2 * d) := by
    rw [pathDist_comm]; exact h1
  refine abs_toReal_sub_le hd ?_ ?_
  · exact (G.pathDist_triangle x x' y').trans (by gcongr)
  · exact (G.pathDist_triangle x' x y').trans (by gcongr)

/-! ### Lemma 4.3 (a): separation of the layers -/

open Classical in
/-- `min (ϱ L ^ i - 1, dist (x, Ω_iᶜ))`, the truncated distance to the complement of `Ω_i`. -/
noncomputable def sepRaw (i : ℕ) (x : Torus d (N₀ * L ^ k)) : ℝ :=
  (insert (ϱ * (L : ℝ) ^ i - 1)
    ((Finset.univ.filter fun z => z ∉ G.Ω i).image
      (Green.torusDist d (N₀ * L ^ k) x))).inf' (Finset.insert_nonempty _ _) id

theorem le_sepRaw_iff (i : ℕ) (x : Torus d (N₀ * L ^ k)) (t : ℝ) :
    t ≤ G.sepRaw i x ↔ t ≤ ϱ * (L : ℝ) ^ i - 1 ∧
      ∀ z, z ∉ G.Ω i → t ≤ Green.torusDist d (N₀ * L ^ k) x z := by
  classical
  unfold sepRaw
  rw [Finset.le_inf'_iff]
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    id, forall_eq_or_imp, forall_exists_index, and_imp]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun z hz => h2 _ z hz rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun b z hz hb => hb ▸ h2 z hz⟩

theorem sepRaw_le_const (i : ℕ) (x : Torus d (N₀ * L ^ k)) :
    G.sepRaw i x ≤ ϱ * (L : ℝ) ^ i - 1 :=
  ((G.le_sepRaw_iff i x _).1 le_rfl).1

theorem sepRaw_le_dist (i : ℕ) (x z : Torus d (N₀ * L ^ k)) (hz : z ∉ G.Ω i) :
    G.sepRaw i x ≤ Green.torusDist d (N₀ * L ^ k) x z :=
  ((G.le_sepRaw_iff i x _).1 le_rfl).2 z hz

theorem sepRaw_nonneg (hϱ : 1 ≤ ϱ) (i : ℕ) (x : Torus d (N₀ * L ^ k)) : 0 ≤ G.sepRaw i x := by
  rw [le_sepRaw_iff]
  refine ⟨?_, fun z _ => torusDist_nonneg' x z⟩
  have hL : (1 : ℝ) ≤ (L : ℝ) ^ i :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  nlinarith

theorem sepRaw_eq_zero (i : ℕ) {x : Torus d (N₀ * L ^ k)} (hx : x ∉ G.Ω i) (hϱ : 1 ≤ ϱ) :
    G.sepRaw i x = 0 := by
  refine le_antisymm ?_ (G.sepRaw_nonneg hϱ i x)
  have := G.sepRaw_le_dist i x x hx
  rwa [torusDist_self'] at this

theorem sepRaw_lipschitz (i : ℕ) (x x' : Torus d (N₀ * L ^ k)) :
    G.sepRaw i x ≤ G.sepRaw i x' + Green.torusDist d (N₀ * L ^ k) x x' := by
  have h : G.sepRaw i x - Green.torusDist d (N₀ * L ^ k) x x' ≤ G.sepRaw i x' := by
    rw [le_sepRaw_iff]
    refine ⟨?_, fun z hz => ?_⟩
    · linarith [G.sepRaw_le_const i x, torusDist_nonneg' (d := d) (L := L) (N₀ := N₀) (k := k) x x']
    · have h1 := G.sepRaw_le_dist i x z hz
      have h2 := torusDist_triangle' x x' z
      linarith
  linarith

/-- Near `Ω_{i+1}` the truncation is active: `sepRaw i x = ϱ L ^ i - 1`. -/
theorem sepRaw_eq_const {i : ℕ} (hi : 1 ≤ i) (hik : i < k) {x x'' : Torus d (N₀ * L ^ k)}
    (hx'' : x'' ∈ G.Ω (i + 1)) (hd : Green.torusDist d (N₀ * L ^ k) x x'' ≤ 1) :
    G.sepRaw i x = ϱ * (L : ℝ) ^ i - 1 := by
  refine le_antisymm (G.sepRaw_le_const i x) ?_
  rw [le_sepRaw_iff]
  refine ⟨le_rfl, fun z hz => ?_⟩
  have h1 := G.separation i hi hik z hz x'' hx''
  have h2 := torusDist_triangle' x'' x z
  rw [torusDist_comm' x'' x] at h2
  rw [torusDist_comm' z x''] at h1
  linarith

/-- The truncated, scaled distance `ψ_i = sepRaw i / L ^ i`. -/
noncomputable def sepFn (i : ℕ) (x : Torus d (N₀ * L ^ k)) : ℝ := G.sepRaw i x / (L : ℝ) ^ i

theorem abs_sepFn_sub_le (i : ℕ) {x x' : Torus d (N₀ * L ^ k)} (hadj : Adj x x') :
    |G.sepFn i x - G.sepFn i x'| ≤ 1 / (L : ℝ) ^ i := by
  have hL : (0 : ℝ) < (L : ℝ) ^ i := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have h1 := G.sepRaw_lipschitz i x x'
  have h2 := G.sepRaw_lipschitz i x' x
  have d1 := hadj.torusDist_le
  have d2 : Green.torusDist d (N₀ * L ^ k) x' x ≤ 1 := by rw [torusDist_comm']; exact d1
  have key : |G.sepRaw i x - G.sepRaw i x'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  unfold sepFn
  rw [← sub_div, abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right key hL.le

/-- If `ψ_i` varies along a bond of `Ω₁` (`1 ≤ i < k`), the bond lies at the top layer `i`. -/
theorem layerIndex_max_of_sepFn_ne (hϱ : 1 ≤ ϱ) {i : ℕ} (hi : 1 ≤ i) (hik : i < k)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hx' : x' ∈ G.Ω 1) (hadj : Adj x x')
    (hne : G.sepFn i x ≠ G.sepFn i x') : max (G.layerIndex x) (G.layerIndex x') = i := by
  have hne' : G.sepRaw i x ≠ G.sepRaw i x' := fun h => hne (by unfold sepFn; rw [h])
  have hd : Green.torusDist d (N₀ * L ^ k) x x' ≤ 1 := hadj.torusDist_le
  have hd' : Green.torusDist d (N₀ * L ^ k) x' x ≤ 1 := by rw [torusDist_comm']; exact hd
  -- neither endpoint lies in `Ω_{i+1}`
  have hxn : x ∉ G.Ω (i + 1) := fun hm =>
    hne' ((G.sepRaw_eq_const hi hik hm (by rw [torusDist_self']; norm_num)).trans
      (G.sepRaw_eq_const hi hik hm hd').symm)
  have hxn' : x' ∉ G.Ω (i + 1) := fun hm =>
    hne' ((G.sepRaw_eq_const hi hik hm hd).trans
      (G.sepRaw_eq_const hi hik hm (by rw [torusDist_self']; norm_num)).symm)
  -- one endpoint lies in `Ω_i`
  have hone : x ∈ G.Ω i ∨ x' ∈ G.Ω i := by
    by_contra hcon
    push Not at hcon
    exact hne' ((G.sepRaw_eq_zero i hcon.1 hϱ).trans (G.sepRaw_eq_zero i hcon.2 hϱ).symm)
  -- layer indices are at most `i`
  have hle : ∀ w, w ∈ G.Ω 1 → w ∉ G.Ω (i + 1) → G.layerIndex w ≤ i := by
    intro w hw hwn
    obtain ⟨h1, h2, h3⟩ := G.layerIndex_spec hw
    by_contra hcon
    exact hwn (G.Ω_antitone (by omega) (by omega) (by omega) (G.mem_layer.1 h3).1)
  have hlay : ∀ w, w ∈ G.Ω i → w ∉ G.Ω (i + 1) → G.layerIndex w = i := fun w hw hwn =>
    G.layerIndex_eq hi hik.le (G.mem_layer.2 ⟨hw, hwn⟩)
  rcases hone with h | h
  · have := hlay x h hxn
    have := hle x' hx' hxn'
    omega
  · have := hlay x' h hxn'
    have := hle x hx hxn
    omega

theorem bondCost_eq_of_max {x x' : Torus d (N₀ * L ^ k)} {M : ℕ}
    (h : max (G.layerIndex x) (G.layerIndex x') = M) : G.bondCost x x' = 1 / (L : ℝ) ^ M := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  unfold bondCost spacing
  rw [← h]
  rcases le_total (G.layerIndex x) (G.layerIndex x') with hle | hle
  · rw [max_eq_right hle, max_eq_right (pow_le_pow_right₀ hL hle)]
  · rw [max_eq_left hle, max_eq_left (pow_le_pow_right₀ hL hle)]

/-- The sum of the truncated distances over the intermediate layers. -/
noncomputable def sepSum (j j' : ℕ) (x : Torus d (N₀ * L ^ k)) : ℝ :=
  ∑ i ∈ Finset.Ioo j j', G.sepFn i x

theorem sepSum_lipschitz (hϱ : 1 ≤ ϱ) {j j' : ℕ} (hj : 1 ≤ j) (hj' : j' ≤ k) :
    ∀ x x', x ∈ G.Ω 1 → x' ∈ G.Ω 1 → Adj x x' →
      |G.sepSum j j' x - G.sepSum j j' x'| ≤ G.bondCost x x' := by
  intro x x' hx hx' hadj
  unfold sepSum
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  set M := max (G.layerIndex x) (G.layerIndex x') with hM
  have hzero : ∀ i ∈ Finset.Ioo j j', i ≠ M → |G.sepFn i x - G.sepFn i x'| = 0 := by
    intro i hi hiM
    have hi' := Finset.mem_Ioo.1 hi
    by_contra hc
    have hne : G.sepFn i x ≠ G.sepFn i x' := fun h => hc (by rw [h]; simp)
    exact hiM (G.layerIndex_max_of_sepFn_ne hϱ (by omega) (by omega) hx hx' hadj hne).symm
  by_cases hMI : M ∈ Finset.Ioo j j'
  · rw [Finset.sum_eq_single_of_mem M hMI (fun i hi hiM => (hzero i hi hiM))]
    rw [G.bondCost_eq_of_max hM.symm]
    exact G.abs_sepFn_sub_le M hadj
  · rw [Finset.sum_eq_zero (fun i hi => hzero i hi (fun h => hMI (h ▸ hi)))]
    exact G.bondCost_nonneg x x'

/-- **Lemma 4.3 (a), separation of the layers.** If `y` lies in layer `j` and `y'` in layer `j' ≥ j`
then `d(y, y') ≥ (ϱ - 1) (j' - j - 1)`. -/
theorem pathDist_separation_le (hϱ : 1 ≤ ϱ) {j j' : ℕ} (hj : 1 ≤ j) (hj' : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.Ω j') :
    ENNReal.ofReal ((ϱ - 1) * ((j' - j - 1 : ℕ) : ℝ)) ≤ G.pathDist y y' := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (G.ofReal_sub_le_pathDist (G.sepSum j j') (G.sepSum_lipschitz hϱ hj hj') y y')
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hy0 : G.sepSum j j' y = 0 := by
    unfold sepSum
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := Finset.mem_Ioo.1 hi
    have : y ∉ G.Ω i := fun hm =>
      (G.mem_layer.1 hy).2 (G.Ω_antitone (by omega) (by omega) (by omega) hm)
    unfold sepFn
    rw [G.sepRaw_eq_zero i this hϱ, zero_div]
  have hyi : ∀ i ∈ Finset.Ioo j j', ϱ - 1 ≤ G.sepFn i y' := by
    intro i hi
    have hi' := Finset.mem_Ioo.1 hi
    have hmem : y' ∈ G.Ω (i + 1) := G.Ω_antitone (by omega) (by omega) (by omega) hy'
    have hLi : (1 : ℝ) ≤ (L : ℝ) ^ i := one_le_pow₀ hL
    unfold sepFn
    rw [G.sepRaw_eq_const (by omega) (by omega) hmem (by rw [torusDist_self']; norm_num)]
    rw [sub_div, mul_div_assoc, div_self (by positivity : ((L : ℝ) ^ i) ≠ 0)]
    have : 1 / (L : ℝ) ^ i ≤ 1 := by rw [div_le_one (by positivity)]; exact hLi
    linarith
  rw [hy0, sub_zero]
  unfold sepSum
  calc (ϱ - 1) * ((j' - j - 1 : ℕ) : ℝ)
      = ∑ _i ∈ Finset.Ioo j j', (ϱ - 1) := by
        rw [Finset.sum_const, Nat.card_Ioo, nsmul_eq_mul, mul_comm]
    _ ≤ _ := Finset.sum_le_sum hyi

end GeneratingSet

end Balaban.Multiscale
