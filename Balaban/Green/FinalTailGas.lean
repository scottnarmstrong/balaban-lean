/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTailConsts
public import Balaban.Polymer.GasBound
public import Balaban.Polymer.Animals
public import Balaban.Polymer.BlockTorus
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The polymer gas of the large blocks of the last integral (W895, blocker 5, leaf L5)

Leaf L5 of `notes/phase1/FINALPHYS3.md` section 7.  The blocks are the `k`-blocks of the cube
neighbourhood, that is the sites `y` of the block torus `Torus d (M1 N₁ L^(k+1-k))` with
`jBlock x = y` for some `x` in `cubeNbhd`; the family is `blk z = {z}` if `z` is such a block and
`∅` otherwise, so that `hcover` of `FinalTailConsts` holds.  The heavy objects of the gas are the
nonempty sets of blocks connected for the nearest-neighbour graph `blockGraph d m`, with
`zs Z = Z`.  The size is the number of blocks, `d X = |X|`, so `hzd` holds with `c₂ = 1`, `hG3`
with `c = 0`.  Counting of connected sets through a block is lattice-animal counting
(`card_animals_le`): `K₀'' = (2d)²`.  The couplings are left abstract: the entropy `hent` follows
from connected supports with at most `mY` couplings per support and a large decay
`κ'' - κ'`; the decay `hB` is the gas's own hypothesis (the open leaf L4).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section Count

variable {V Zt : Type*} [Fintype Zt] (G : SimpleGraph V) [G.LocallyFinite]

/-- **Counting of connected sets through a vertex.**  If the supports `zs z` are connected, at
most `m` objects have a given support, and the degrees are at most `Δ`, then at most
`m Δ^{2 (v - 1)}` objects have a support of `v` vertices containing `b`. -/
theorem card_filter_conn_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) {zs : Zt → Finset V}
    (hconn : ∀ z, (G.induce (zs z : Set V)).Connected) {m : ℝ}
    (hfib : ∀ T, ((Finset.univ.filter fun z => zs z = T).card : ℝ) ≤ m) (b : V) (v : ℕ) :
    ((Finset.univ.filter fun z => b ∈ zs z ∧ (zs z).card = v).card : ℝ) ≤
      m * (Δ : ℝ) ^ (2 * (v - 1)) := by
  set s := Finset.univ.filter fun z => b ∈ zs z ∧ (zs z).card = v with hs
  have himg : s.image zs ⊆ animals G b v := by
    intro T hT
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hT
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact (mem_animals G).2 ⟨hz.1, hz.2, hconn z⟩
  have hm : 0 ≤ m := le_trans (Nat.cast_nonneg _) (hfib ∅)
  have h1 : (s.card : ℝ) = ∑ a ∈ s.image zs, ((s.filter fun x => zs x = a).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image zs s
  have h2 : ∀ a ∈ s.image zs, ((s.filter fun x => zs x = a).card : ℝ) ≤ m := by
    intro a _
    refine le_trans ?_ (hfib a)
    exact_mod_cast Finset.card_le_card (fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hx.2)
  calc (s.card : ℝ) ≤ ∑ a ∈ s.image zs, m := h1 ▸ Finset.sum_le_sum h2
    _ = ((s.image zs).card : ℝ) * m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((animals G b v).card : ℝ) * m := by
        gcongr
    _ ≤ (Δ : ℝ) ^ (2 * (v - 1)) * m := by
        gcongr
        exact_mod_cast card_animals_le G hΔ b v
    _ = _ := mul_comm _ _

/-- The counting bound in the form `(m Δ²)^v` of the hypothesis `hcount` of the gas
(`1 ≤ m`, `1 ≤ Δ`). -/
theorem card_filter_conn_le_pow {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (hΔ1 : 1 ≤ Δ)
    {zs : Zt → Finset V} (hconn : ∀ z, (G.induce (zs z : Set V)).Connected) {m : ℝ}
    (hfib : ∀ T, ((Finset.univ.filter fun z => zs z = T).card : ℝ) ≤ m) (hm : 1 ≤ m) (b : V)
    (v : ℕ) :
    ((Finset.univ.filter fun z => b ∈ zs z ∧ (zs z).card = v).card : ℝ) ≤
      (m * (Δ : ℝ) ^ 2) ^ v := by
  have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ1
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · have : (Finset.univ.filter fun z => b ∈ zs z ∧ (zs z).card = 0) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact absurd (Finset.card_eq_zero.1 hz.2 ▸ hz.1) (Finset.notMem_empty _)
    rw [this]; simp
  · refine (card_filter_conn_le G hΔ hconn hfib b v).trans ?_
    rw [mul_pow, ← pow_mul]
    have h1 : m ≤ m ^ v := le_self_pow₀ hm hv.ne'
    have h2 : (Δ : ℝ) ^ (2 * (v - 1)) ≤ (Δ : ℝ) ^ (2 * v) :=
      pow_le_pow_right₀ hΔr (by omega)
    have h0 : (0 : ℝ) ≤ (Δ : ℝ) ^ (2 * (v - 1)) := by positivity
    calc m * (Δ : ℝ) ^ (2 * (v - 1)) ≤ m ^ v * (Δ : ℝ) ^ (2 * v) :=
          mul_le_mul h1 h2 h0 (by positivity)
      _ = _ := by rw [mul_comm 2 v]

end Count

section Entropy

variable {V Yt : Type*} [Fintype V] [Fintype Yt] (G : SimpleGraph V) [G.LocallyFinite]

/-- **Entropy of the couplings.**  If the supports `cy y` are nonempty and connected, at most `mY`
couplings have a given support, and the decay `κ` is at least `log (mY Δ²) + 3`, then the
entropy sum through a vertex is at most `1` (hypothesis `hent` of the gas with `K₀' = 1`). -/
theorem coupling_entropy_le_one {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (hΔ1 : 1 ≤ Δ)
    {cy : Yt → Finset V} (hne : ∀ y, (cy y).Nonempty)
    (hconn : ∀ y, (G.induce (cy y : Set V)).Connected) {mY κ : ℝ}
    (hfib : ∀ T, ((Finset.univ.filter fun y => cy y = T).card : ℝ) ≤ mY) (hm : 1 ≤ mY)
    (hκ : Real.log (mY * (Δ : ℝ) ^ 2) + 3 ≤ κ) (b : V) :
    ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y), Real.exp (-κ * ((cy y).card : ℝ)) ≤ 1 := by
  have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ1
  have hK0 : (1 : ℝ) ≤ mY * (Δ : ℝ) ^ 2 := by nlinarith
  have h := heavy_entropy (zs := cy) (K0 := mY * (Δ : ℝ) ^ 2) (c1 := 0) (lam := κ) le_rfl hK0
    hne (fun b v => card_filter_conn_le_pow G hΔ hΔ1 hconn hfib hm b v) (by linarith) b
  refine h.trans ?_
  rw [Real.exp_le_one_iff]
  norm_num

end Entropy

section GasData

variable {V : Type*}

/-- **Size subadditivity (`hG3`) for the size `|X|`**, with `c = 0`: the number of blocks of a
union is at most the sum of the numbers of blocks. -/
theorem card_unionCs_le {E : Type*} (cs : E → Finset V) (C : Finset E) :
    (((unionCs cs C).card : ℕ) : ℝ) ≤ ∑ t ∈ C, ((cs t).card : ℝ) := by
  exact_mod_cast Finset.card_biUnion_le

end GasData

end Balaban.Polymer

namespace Balaban.Green

open Balaban Balaban.Multiscale Balaban.LargeField MeasureTheory Balaban.Polymer

section Blocks

variable {d M1 N₁ L k : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-- **The block family of the last step (leaf L5 (1)).**  The family
`blk z = {z}` if `z` is the `k`-block `jBlock x` of a site `x` of the cube neighbourhood and
`blk z = ∅` otherwise, indexed by all sites of the block torus, satisfies `hcover` of
`FinalTailConsts`: its blocks cover exactly the `k`-blocks of the neighbourhood. -/
theorem blk_hcover (c n : ℕ) (y0 : Torus d n) :
    ∀ y, (∃ x ∈ cubeNbhd M1 N₁ L (k + 1) c n 0 y0,
        jBlock d L (M1 * N₁) (k + 1) k x = y) ↔
      ∃ z, y ∈ (fun z : Torus d (M1 * N₁ * L ^ (k + 1 - k)) =>
        ({z} : Finset (Torus d (M1 * N₁ * L ^ (k + 1 - k)))).filter
          (fun y => ∃ x ∈ cubeNbhd M1 N₁ L (k + 1) c n 0 y0,
            jBlock d L (M1 * N₁) (k + 1) k x = y)) z := by
  intro y
  constructor
  · intro h
    exact ⟨y, by simp [h]⟩
  · rintro ⟨z, hz⟩
    simp only [Finset.mem_filter, Finset.mem_singleton] at hz
    exact hz.2

/-- The blocks of the family are pairwise disjoint (indeed `blk z ⊆ {z}`), and have at most one
site. -/
theorem blk_disjoint_card (c n : ℕ) (y0 : Torus d n) :
    (∀ z z' : Torus d (M1 * N₁ * L ^ (k + 1 - k)), z ≠ z' →
      Disjoint (({z} : Finset (Torus d (M1 * N₁ * L ^ (k + 1 - k)))).filter
          (fun y => ∃ x ∈ cubeNbhd M1 N₁ L (k + 1) c n 0 y0,
            jBlock d L (M1 * N₁) (k + 1) k x = y))
        (({z'} : Finset (Torus d (M1 * N₁ * L ^ (k + 1 - k)))).filter
          (fun y => ∃ x ∈ cubeNbhd M1 N₁ L (k + 1) c n 0 y0,
            jBlock d L (M1 * N₁) (k + 1) k x = y))) ∧
    ∀ z : Torus d (M1 * N₁ * L ^ (k + 1 - k)),
      (({z} : Finset (Torus d (M1 * N₁ * L ^ (k + 1 - k)))).filter
          (fun y => ∃ x ∈ cubeNbhd M1 N₁ L (k + 1) c n 0 y0,
            jBlock d L (M1 * N₁) (k + 1) k x = y)).card ≤ 1 := by
  refine ⟨fun z z' hne => ?_, fun z => ?_⟩
  · refine Finset.disjoint_left.2 fun y hy hy' => hne ?_
    simp only [Finset.mem_filter, Finset.mem_singleton] at hy hy'
    exact hy.1.symm.trans hy'.1
  · exact (Finset.card_filter_le _ _).trans (by simp)

end Blocks

section Heavy

variable {d m : ℕ} [NeZero m] {Zt : Type*} [Fintype Zt]

/-- **Counting of heavy objects through a block (leaf L5 (2), `hcount`).**  The heavy objects are
nonempty sets `zs Z` of blocks of the torus, connected for the nearest-neighbour graph
`blockGraph d m`, with `zs` injective.  The number of those through a block `b` with `v` blocks is
at most `((2d)²)^v` (lattice animals). -/
theorem blockGraph_hcount (hd : 1 ≤ d) {zs : Zt → Finset (Torus d m)}
    (hconn : ∀ z, ((blockGraph d m).induce (zs z : Set (Torus d m))).Connected)
    (hinj : Function.Injective zs) (b : Torus d m) (v : ℕ) :
    ((Finset.univ.filter fun z => b ∈ zs z ∧ (zs z).card = v).card : ℝ) ≤
      (((2 * d : ℕ) : ℝ) ^ 2) ^ v := by
  have h := card_filter_conn_le_pow (blockGraph d m) (Δ := 2 * d) (blockGraph_degree_le d m)
    (by omega) hconn (m := 1) (fun T => by
      have : (Finset.univ.filter fun z => zs z = T).card ≤ 1 :=
        Finset.card_le_one.2 fun a ha a' ha' => hinj (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
          exact ha.trans ha'.symm)
      have h2 : ((Finset.univ.filter fun z => zs z = T).card : ℝ) ≤ 1 := by
        exact_mod_cast this
      convert h2) le_rfl b v
  convert (by simpa using h : _ ≤ (((2 * d : ℕ) : ℝ) ^ 2) ^ v)

end Heavy

end Balaban.Green

