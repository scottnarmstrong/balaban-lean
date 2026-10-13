/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.KF0KilledWalks
public import Balaban.LargeField.Base.KF0BlockSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Attenuation of the mean induced by bad blocks: per-core bound, shell sum, frozen radii

Source: `notes/phase1/KF0-LINK.md`, section 1 (L38.1)-(L38.3).

Setting: the unit lattice is the torus `Torus d ℓ`; the blocks of side `s` are indexed by
`Torus d m` via `blockMap s m`; `B` is a fixed finite set of bad blocks, `D = siteUnion s m B` the
sites of the holes, `kwOp d ℓ ν D` the good-region operator `K_G`.  Bond amplitudes
`w x y` (real numbers) and amplitudes `aQ Q ≥ 0` are fixed; everything is scalar valued (one
tangent coordinate) and applies coordinatewise.

Contents.
* `blockSites`, `coreSource`, `coreMean`, `blockDist`: the sites of a block, the per-core
  boundary source `J_Q(x) = ∑_{y ∈ Q} A(x, y) w(x, y)` at good sites `x`, the per-core mean
  `m_Q = -K_G⁻¹ J_Q`, and the `ℓ¹` distance from a site to a block (a natural number, the minimum
  of `torusDistNat x y` over the sites `y` of the block).
* T1: `sum_coreSource` (the sum over `B` of the per-core sources is the full boundary source),
  `coreSource_abs_le` (bound `2d aQ`), `coreSource_support`, `coreMean_bound`
  (`|m_Q(x)| ≤ (2d aQ/ν) q^(dist(x,Q) - 1)`, natural-number subtraction), `coreMean_bound_q`,
  `coreMean_bound_gap` (the constant `2d/(ν_* q_*)` with `ν ≥ ν_*`).
* T2: `shellSum` (the sum `D(d, q) = ∑_{r ≥ 0} (2r+1)^d q^(r/2)`), `shell_summable`,
  `card_sphere_le`, `card_blocks_dist_le`.
* T3: `cL`, `freezeRadius` (the radius `R_Q` of (L38.2)), `radius_bound`, `freezeRadius_bound`.
* T4: `mean_outside_collars` (L38.3).
* T5: `mean_outside_collars_instance`.

Not proved here: the bad set and the amplitudes are fixed; the collar budget (L38.4), the closure
graph, the integrated collar potential and the one-scale theorem are NOT proved here.
-/

@[expose] public section

open Matrix Finset Balaban Balaban.Green

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

variable {d ℓ m : ℕ} [NeZero ℓ] [NeZero m]

/-! ### Blocks, per-core source, per-core mean, distance -/

/-- The sites of the block `Q` of side `s`. -/
def blockSites (s m : ℕ) (Q : Torus d m) : Finset (Torus d ℓ) :=
  Finset.univ.filter fun x => blockMap s m x = Q

theorem mem_blockSites {s : ℕ} {Q : Torus d m} {y : Torus d ℓ} :
    y ∈ blockSites (ℓ := ℓ) s m Q ↔ blockMap s m y = Q := by
  simp [blockSites]

/-- The per-core boundary source: at a good site `x`, `J_Q(x) = ∑_{y ∈ Q} A(x, y) w(x, y)` (the
crossing bonds from `x` into the block `Q`, with amplitudes `w`); zero at the sites of `D`. -/
noncomputable def coreSource (s : ℕ) (w : Torus d ℓ → Torus d ℓ → ℝ) (B : Finset (Torus d m))
    (Q : Torus d m) (x : Torus d ℓ) : ℝ :=
  if x ∈ siteUnion (ℓ := ℓ) s m B then 0 else ∑ y ∈ blockSites (ℓ := ℓ) s m Q, kwAdj d ℓ x y * w x y

/-- The full boundary source: at a good site `x`, `∑_{y ∈ D} A(x, y) w(x, y)`. -/
noncomputable def fullSource (s : ℕ) (w : Torus d ℓ → Torus d ℓ → ℝ) (B : Finset (Torus d m))
    (x : Torus d ℓ) : ℝ :=
  if x ∈ siteUnion (ℓ := ℓ) s m B then 0 else ∑ y ∈ siteUnion (ℓ := ℓ) s m B, kwAdj d ℓ x y * w x y

/-- The per-core mean `m_Q = -K_G⁻¹ J_Q`. -/
noncomputable def coreMean (ν : ℝ) (s : ℕ) (w : Torus d ℓ → Torus d ℓ → ℝ)
    (B : Finset (Torus d m)) (Q : Torus d m) : Torus d ℓ → ℝ :=
  -((kwOp d ℓ ν (siteUnion (ℓ := ℓ) s m B))⁻¹ *ᵥ coreSource s w B Q)

/-- The `ℓ¹` distance on the torus as a natural number. -/
def torusDistNat (d ℓ : ℕ) [NeZero ℓ] (x y : Torus d ℓ) : ℕ :=
  ∑ i, (cycRep (x i - y i)).natAbs

theorem torusDist_eq_natCast (x y : Torus d ℓ) :
    torusDist d ℓ x y = (torusDistNat d ℓ x y : ℝ) := by
  simp [torusDist, torusDistNat]

/-- `dist(x, Q)`: the minimum of the `ℓ¹` distances from `x` to the sites of the block `Q`
(`0` if the block has no site). -/
noncomputable def blockDist (s : ℕ) (x : Torus d ℓ) (Q : Torus d m) : ℕ :=
  sInf (torusDistNat d ℓ x '' (blockSites (ℓ := ℓ) s m Q : Set (Torus d ℓ)))

theorem blockDist_le {s : ℕ} {x y : Torus d ℓ} {Q : Torus d m}
    (hy : y ∈ blockSites (ℓ := ℓ) s m Q) : blockDist s x Q ≤ torusDistNat d ℓ x y :=
  Nat.sInf_le ⟨y, hy, rfl⟩

theorem exists_blockDist {s : ℕ} {Q : Torus d m} (x : Torus d ℓ)
    (h : (blockSites (ℓ := ℓ) s m Q).Nonempty) :
    ∃ y ∈ blockSites (ℓ := ℓ) s m Q, torusDistNat d ℓ x y = blockDist s x Q := by
  have : (torusDistNat d ℓ x '' (blockSites (ℓ := ℓ) s m Q : Set (Torus d ℓ))).Nonempty :=
    Set.Nonempty.image _ (Finset.coe_nonempty.2 h)
  obtain ⟨y, hy, hy2⟩ := Nat.sInf_mem this
  exact ⟨y, hy, hy2⟩

/-! ### T1 -/

theorem sum_coreSource (s : ℕ) (w : Torus d ℓ → Torus d ℓ → ℝ) (B : Finset (Torus d m))
    (x : Torus d ℓ) : ∑ Q ∈ B, coreSource s w B Q x = fullSource s w B x := by
  unfold coreSource fullSource
  by_cases hx : x ∈ siteUnion (ℓ := ℓ) s m B
  · simp [hx]
  · simp only [hx, ite_false]
    rw [← Finset.sum_fiberwise_of_maps_to (s := siteUnion (ℓ := ℓ) s m B) (t := B)
      (g := blockMap s m) (fun y hy => by simpa [siteUnion] using hy)]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext y
    simp only [Finset.mem_filter, mem_blockSites, siteUnion, Finset.mem_univ, true_and]
    constructor <;> intro h <;> simp_all

theorem coreSource_abs_le {s : ℕ} {w : Torus d ℓ → Torus d ℓ → ℝ} {B : Finset (Torus d m)}
    {Q : Torus d m} {aQ : ℝ} (haQ : 0 ≤ aQ)
    (hw : ∀ x ∉ siteUnion (ℓ := ℓ) s m B, ∀ y ∈ blockSites (ℓ := ℓ) s m Q, |w x y| ≤ aQ)
    (x : Torus d ℓ) : |coreSource s w B Q x| ≤ 2 * d * aQ := by
  unfold coreSource
  split_ifs with hx
  · simp only [abs_zero]; positivity
  · calc |∑ y ∈ blockSites (ℓ := ℓ) s m Q, kwAdj d ℓ x y * w x y|
        ≤ ∑ y ∈ blockSites (ℓ := ℓ) s m Q, |kwAdj d ℓ x y * w x y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ blockSites (ℓ := ℓ) s m Q, kwAdj d ℓ x y * aQ := Finset.sum_le_sum fun y hy => by
          rw [abs_mul, abs_of_nonneg (kwAdj_nonneg x y)]
          exact mul_le_mul_of_nonneg_left (hw x hx y hy) (kwAdj_nonneg x y)
      _ ≤ ∑ y, kwAdj d ℓ x y * aQ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun y _ _ => mul_nonneg (kwAdj_nonneg x y) haQ
      _ = 2 * d * aQ := by rw [← Finset.sum_mul, kwAdj_rowSum]

theorem coreSource_support {s : ℕ} {w : Torus d ℓ → Torus d ℓ → ℝ} {B : Finset (Torus d m)}
    {Q : Torus d m} {x : Torus d ℓ} (h : coreSource s w B Q x ≠ 0) :
    x ∉ siteUnion (ℓ := ℓ) s m B ∧
      ∃ y ∈ blockSites (ℓ := ℓ) s m Q, kwAdj d ℓ x y ≠ 0 := by
  unfold coreSource at h
  split_ifs at h with hx
  · exact absurd rfl h
  · refine ⟨hx, ?_⟩
    obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact ⟨y, hy, left_ne_zero_of_mul hne⟩

/-- The per-core decay with an explicit exponent `t`: if `t = 0` or every site `y'` of the block
satisfies `t + 1 ≤ torusDist x y'`, then `|m_Q(x)| ≤ (2d aQ/ν) q^t`. -/
theorem coreMean_decay {ν : ℝ} (hν : 0 < ν) {s : ℕ} {w : Torus d ℓ → Torus d ℓ → ℝ}
    {B : Finset (Torus d m)} {Q : Torus d m} {aQ : ℝ} (haQ : 0 ≤ aQ)
    (hw : ∀ x ∉ siteUnion (ℓ := ℓ) s m B, ∀ y ∈ blockSites (ℓ := ℓ) s m Q, |w x y| ≤ aQ)
    (x : Torus d ℓ) (t : ℕ)
    (ht : t = 0 ∨ ∀ y ∈ blockSites (ℓ := ℓ) s m Q, (t : ℝ) + 1 ≤ torusDist d ℓ x y) :
    |coreMean ν s w B Q x| ≤ 2 * d * aQ / ν * kwQ d ν ^ t := by
  unfold coreMean
  rw [Pi.neg_apply, abs_neg]
  refine kwOp_inv_mulVec_decay hν _ _ (coreSource_abs_le haQ hw) x t fun y hy => ?_
  obtain ⟨_, y', hy', hadj⟩ := coreSource_support hy
  have h1 := kwAdj_dist_le_one hadj
  have h2 := torusDist_triangle' x y y'
  rcases ht with h0 | h3
  · rw [h0]; simpa using torusDist_nonneg' x y
  · have := h3 y' hy'; linarith

/-- **(L38.1), exponent form.** `|m_Q(x)| ≤ (2d aQ/ν) q^(dist(x,Q) - 1)` with natural-number
subtraction, `q = 2d/(2d+ν)`. -/
theorem coreMean_bound {ν : ℝ} (hν : 0 < ν) {s : ℕ} {w : Torus d ℓ → Torus d ℓ → ℝ}
    {B : Finset (Torus d m)} {Q : Torus d m} {aQ : ℝ} (haQ : 0 ≤ aQ)
    (hw : ∀ x ∉ siteUnion (ℓ := ℓ) s m B, ∀ y ∈ blockSites (ℓ := ℓ) s m Q, |w x y| ≤ aQ)
    (x : Torus d ℓ) :
    |coreMean ν s w B Q x| ≤ 2 * d * aQ / ν * kwQ d ν ^ (blockDist s x Q - 1) := by
  refine coreMean_decay hν haQ hw x _ ?_
  by_cases h0 : blockDist s x Q = 0
  · exact Or.inl (by simp [h0])
  · refine Or.inr fun y hy => ?_
    have h := blockDist_le (x := x) hy
    rw [torusDist_eq_natCast]
    have h' : (blockDist s x Q : ℝ) ≤ torusDistNat d ℓ x y := by exact_mod_cast h
    have : ((blockDist s x Q - 1 : ℕ) : ℝ) = (blockDist s x Q : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 h0)]; simp
    linarith

theorem kwQ_pos (hd : 0 < d) {ν : ℝ} (hν : 0 < ν) : 0 < kwQ d ν := by
  unfold kwQ; positivity

/-- **(L38.1), distance form with constant `2d/(ν₀ q₀)`.**  For `0 < ν₀ ≤ ν`, `q₀ = kwQ d ν₀`:
`|m_Q(x)| ≤ (2d/(ν₀ q₀)) aQ q₀^dist(x,Q)`. -/
theorem coreMean_bound_q {ν₀ ν : ℝ} (hd : 0 < d) (hν₀ : 0 < ν₀) (hle : ν₀ ≤ ν) {s : ℕ}
    {w : Torus d ℓ → Torus d ℓ → ℝ} {B : Finset (Torus d m)} {Q : Torus d m} {aQ : ℝ}
    (haQ : 0 ≤ aQ)
    (hw : ∀ x ∉ siteUnion (ℓ := ℓ) s m B, ∀ y ∈ blockSites (ℓ := ℓ) s m Q, |w x y| ≤ aQ)
    (x : Torus d ℓ) :
    |coreMean ν s w B Q x| ≤ 2 * d / (ν₀ * kwQ d ν₀) * aQ * kwQ d ν₀ ^ blockDist s x Q := by
  have hν : 0 < ν := hν₀.trans_le hle
  have hq0 := kwQ_pos hd hν₀
  have hq := kwQ_pos hd hν
  have hq1 : kwQ d ν₀ ≤ 1 := (kwQ_lt_one hν₀).le
  have hqq : kwQ d ν ≤ kwQ d ν₀ := by
    unfold kwQ
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hconst : 1 / (ν * kwQ d ν) ≤ 1 / (ν₀ * kwQ d ν₀) := by
    have : ν₀ * kwQ d ν₀ ≤ ν * kwQ d ν := by
      unfold kwQ
      rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 2 * d by positivity) (show (0:ℝ) ≤ 2 * d by positivity)) (sub_nonneg.2 hle)]
    exact one_div_le_one_div_of_le (by positivity) this
  have h1 := coreMean_bound hν haQ hw x
  set n := blockDist s x Q with hn
  have hpow : kwQ d ν ^ (n - 1) ≤ kwQ d ν₀ ^ n / kwQ d ν := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0]; simp
      exact (one_le_inv₀ hq).2 (hqq.trans hq1)
    · rw [le_div_iff₀ hq, ← pow_succ, Nat.sub_add_cancel h0]
      exact pow_le_pow_left₀ hq.le hqq n
  calc |coreMean ν s w B Q x| ≤ 2 * d * aQ / ν * kwQ d ν ^ (n - 1) := h1
    _ ≤ 2 * d * aQ / ν * (kwQ d ν₀ ^ n / kwQ d ν) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 2 * d * aQ * (1 / (ν * kwQ d ν)) * kwQ d ν₀ ^ n := by field_simp
    _ ≤ 2 * d * aQ * (1 / (ν₀ * kwQ d ν₀)) * kwQ d ν₀ ^ n := by
        gcongr
    _ = _ := by ring

/-- **(L38.1) with the gap.**  For `ν ≥ ν_* = kf0Gap L`, `q_* = kwQ d ν_*`. -/
theorem coreMean_bound_gap {L : ℕ} (hL : 0 < L) {ν : ℝ} (hd : 0 < d) (hle : kf0Gap L ≤ ν)
    {s : ℕ} {w : Torus d ℓ → Torus d ℓ → ℝ} {B : Finset (Torus d m)} {Q : Torus d m} {aQ : ℝ}
    (haQ : 0 ≤ aQ)
    (hw : ∀ x ∉ siteUnion (ℓ := ℓ) s m B, ∀ y ∈ blockSites (ℓ := ℓ) s m Q, |w x y| ≤ aQ)
    (x : Torus d ℓ) :
    |coreMean ν s w B Q x| ≤
      2 * d / (kf0Gap L * kwQ d (kf0Gap L)) * aQ * kwQ d (kf0Gap L) ^ blockDist s x Q :=
  coreMean_bound_q hd (kf0Gap_pos hL) hle haQ hw x

/-! ### T2: the shell sum and the count of blocks at a given distance -/

/-- `D(d, q) = ∑_{r ≥ 0} (2r+1)^d q^(r/2)`. -/
noncomputable def shellSum (d : ℕ) (q : ℝ) : ℝ :=
  ∑' r : ℕ, (2 * (r : ℝ) + 1) ^ d * q ^ ((r : ℝ) / 2)

theorem rpow_half_nat {q : ℝ} (hq : 0 ≤ q) (r : ℕ) : q ^ ((r : ℝ) / 2) = Real.sqrt q ^ r := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq]; ring_nf

theorem shell_summable {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun r : ℕ => (2 * (r : ℝ) + 1) ^ d * q ^ ((r : ℝ) / 2) := by
  have hs : Real.sqrt q < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using hq1
  have hs0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have h1 : Summable fun r : ℕ => (r : ℝ) ^ d * Real.sqrt q ^ r :=
    summable_pow_mul_geometric_of_norm_lt_one d (by rwa [Real.norm_eq_abs, abs_of_nonneg hs0])
  have h2 : Summable fun r : ℕ => Real.sqrt q ^ r :=
    summable_geometric_of_lt_one hs0 hs
  refine Summable.of_nonneg_of_le (fun r => ?_) (fun r => ?_)
    ((h1.mul_left (3 ^ d)).add h2)
  · positivity
  · rw [rpow_half_nat hq0]
    have : (2 * (r : ℝ) + 1) ^ d ≤ 3 ^ d * (r : ℝ) ^ d + 1 := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; simp
      · have hr : (1 : ℝ) ≤ r := by exact_mod_cast h
        calc (2 * (r : ℝ) + 1) ^ d ≤ (3 * r) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
          _ = 3 ^ d * (r : ℝ) ^ d := mul_pow _ _ _
          _ ≤ _ := by linarith
    calc (2 * (r : ℝ) + 1) ^ d * Real.sqrt q ^ r
        ≤ (3 ^ d * (r : ℝ) ^ d + 1) * Real.sqrt q ^ r :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 3 ^ d * ((r : ℝ) ^ d * Real.sqrt q ^ r) + Real.sqrt q ^ r := by ring

theorem shellSum_pos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 < shellSum d q := by
  unfold shellSum
  have h := (shell_summable (d := d) hq0 hq1)
  calc (0 : ℝ) < (2 * ((0 : ℕ) : ℝ) + 1) ^ d * q ^ (((0 : ℕ) : ℝ) / 2) := by simp
    _ ≤ _ := h.le_tsum 0 (fun r _ => by positivity)

/-- At most `(2r+1)^d` sites at `ℓ¹` distance exactly `r` from `x`. -/
theorem card_sphere_le (x : Torus d ℓ) (r : ℕ) :
    (Finset.univ.filter fun y : Torus d ℓ => torusDistNat d ℓ x y = r).card ≤ (2 * r + 1) ^ d := by
  have hcard : (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(r : ℤ)) r).card = (2 * r + 1) ^ d := by
    rw [Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1; omega
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun y i => cycRep (x i - y i)) ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have : (cycRep (x i - y i)).natAbs ≤ r := by
      rw [← hy]
      exact Finset.single_le_sum (f := fun i => (cycRep (x i - y i)).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  · intro y _ y' _ h
    funext i
    have := cycRep_injective (congrFun h i)
    simpa using this

/-- The blocks of `B` that have a site and are at distance exactly `r` from `x` number at most
`(2r+1)^d` (distinct blocks give distinct sites). -/
theorem card_blocks_dist_le (s : ℕ) (x : Torus d ℓ) (B : Finset (Torus d m)) (r : ℕ) :
    ((B.filter fun Q => (blockSites (ℓ := ℓ) s m Q).Nonempty).filter
      fun Q => blockDist s x Q = r).card ≤ (2 * r + 1) ^ d := by
  refine le_trans (Finset.card_le_card_of_forall_subsingleton
    (t := Finset.univ.filter fun y : Torus d ℓ => torusDistNat d ℓ x y = r)
    (fun Q y => y ∈ blockSites (ℓ := ℓ) s m Q ∧ torusDistNat d ℓ x y = r) ?_ ?_)
    (card_sphere_le x r)
  · intro Q hQ
    simp only [Finset.mem_filter] at hQ
    obtain ⟨y, hy, hyd⟩ := exists_blockDist x hQ.1.2
    exact ⟨y, by simp [hyd, hQ.2], hy, by rw [hyd, hQ.2]⟩
  · intro y _ Q hQ Q' hQ'
    have h1 := mem_blockSites.1 hQ.2.1
    have h2 := mem_blockSites.1 hQ'.2.1
    exact h1.symm.trans h2

/-! ### T3: the frozen radii -/

/-- `C_L = 4d D(d, q) / (ν q)` with `q = kwQ d ν`. -/
noncomputable def cL (d : ℕ) (ν : ℝ) : ℝ := 4 * d * shellSum d (kwQ d ν) / (ν * kwQ d ν)

/-- The frozen radius `R_Q = ⌈(2/η) log₊(C_L √β a_Q log(βa))⌉₊`, `η = -log q`, `q = kwQ d ν`. -/
noncomputable def freezeRadius (d : ℕ) (ν β a aQ : ℝ) : ℕ :=
  ⌈2 / (-Real.log (kwQ d ν)) *
      max (Real.log (cL d ν * Real.sqrt β * aQ * Real.log (β * a))) 0⌉₊

theorem cL_pos (hd : 0 < d) {ν : ℝ} (hν : 0 < ν) : 0 < cL d ν := by
  have hq0 := kwQ_pos hd hν
  unfold cL
  have := shellSum_pos (d := d) hq0.le (kwQ_lt_one hν)
  have : (0:ℝ) < d := by exact_mod_cast hd
  have := mul_pos hν hq0
  positivity

/-- Generic form of the implication of (L38.2). -/
theorem radius_bound {q C β aQ Lg : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 0 < C) (haQ : 0 ≤ aQ)
    (hLg : 0 < Lg) (r : ℕ)
    (hr : ⌈2 / (-Real.log q) * max (Real.log (C * Real.sqrt β * aQ * Lg)) 0⌉₊ ≤ r) :
    Real.sqrt β * aQ * q ^ ((r : ℝ) / 2) ≤ 1 / (C * Lg) := by
  set K := C * Real.sqrt β * aQ * Lg with hK
  have hK0 : 0 ≤ K := by positivity
  have heta : 0 < -Real.log q := neg_pos.2 (Real.log_neg hq0 hq1)
  have key : K * q ^ ((r : ℝ) / 2) ≤ 1 := by
    rcases hK0.eq_or_lt with h | h
    · rw [← h]; simp
    · have h1 : 2 / (-Real.log q) * max (Real.log K) 0 ≤ r :=
        (Nat.le_ceil _).trans (by exact_mod_cast hr)
      have h2 : Real.log K ≤ (-Real.log q) * ((r : ℝ) / 2) := by
        have := (le_max_left (Real.log K) 0)
        rw [div_mul_eq_mul_div, div_le_iff₀ heta] at h1
        nlinarith [mul_le_mul_of_nonneg_left this (show (0:ℝ) ≤ 2 by norm_num)]
      have h3 : q ^ ((r : ℝ) / 2) = Real.exp (Real.log q * ((r : ℝ) / 2)) := by
        rw [Real.rpow_def_of_pos hq0, mul_comm]
      have h4 : K * q ^ ((r : ℝ) / 2) = Real.exp (Real.log K + Real.log q * ((r : ℝ) / 2)) := by
        rw [Real.exp_add, Real.exp_log h, h3]
      rw [h4]
      calc _ ≤ Real.exp 0 := Real.exp_le_exp.2 (by nlinarith)
        _ = 1 := Real.exp_zero
  have hCL : 0 < C * Lg := by positivity
  rw [le_div_iff₀ hCL]
  calc Real.sqrt β * aQ * q ^ ((r : ℝ) / 2) * (C * Lg) = K * q ^ ((r : ℝ) / 2) := by
        rw [hK]; ring
    _ ≤ 1 := key

/-- **(L38.2).**  For `r ≥ R_Q`: `√β a_Q q^(r/2) ≤ 1/(C_L log(βa))`. -/
theorem freezeRadius_bound {d : ℕ} (hd : 0 < d) {ν β a aQ : ℝ} (hν : 0 < ν) (haQ : 0 ≤ aQ)
    (hlog : 0 < Real.log (β * a)) (r : ℕ) (hr : freezeRadius d ν β a aQ ≤ r) :
    Real.sqrt β * aQ * kwQ d ν ^ ((r : ℝ) / 2) ≤ 1 / (cL d ν * Real.log (β * a)) := by
  have hq0 := kwQ_pos hd hν
  have hC : 0 < cL d ν := cL_pos hd hν
  exact radius_bound hq0 (kwQ_lt_one hν) hC haQ hlog r hr

/-! ### T4: the Gaussian-unit bound outside all collars -/

theorem coreSource_eq_zero_of_empty {s : ℕ} (w : Torus d ℓ → Torus d ℓ → ℝ)
    (B : Finset (Torus d m)) {Q : Torus d m} (h : ¬ (blockSites (ℓ := ℓ) s m Q).Nonempty) :
    coreSource s w B Q = 0 := by
  funext x
  rw [Finset.not_nonempty_iff_eq_empty] at h
  simp [coreSource, h]

theorem rpow_half_mul_self {q : ℝ} (hq : 0 < q) (n : ℕ) :
    q ^ ((n : ℝ) / 2) * q ^ ((n : ℝ) / 2) = q ^ n := by
  rw [← Real.rpow_add hq, show (n : ℝ) / 2 + n / 2 = n by ring, Real.rpow_natCast]

/-- **(L38.3).**  Fix the bad set `B`, the bond amplitudes `w` and the amplitudes `aQ`.  If `x` is
at distance at least `R_Q` from every site of every block `Q ∈ B`, then
`√β |∑_{Q∈B} m_Q(x)| ≤ 1/(2 log(βa))`, with no factor `|B|`. -/
theorem mean_outside_collars {ν β a : ℝ} (hd : 0 < d) (hν : 0 < ν)
    (hlog : 0 < Real.log (β * a)) {s : ℕ} {w : Torus d ℓ → Torus d ℓ → ℝ}
    {B : Finset (Torus d m)} {aQ : Torus d m → ℝ} (haQ : ∀ Q ∈ B, 0 ≤ aQ Q)
    (hw : ∀ Q ∈ B, ∀ x ∉ siteUnion (ℓ := ℓ) s m B, ∀ y ∈ blockSites (ℓ := ℓ) s m Q,
      |w x y| ≤ aQ Q)
    (x : Torus d ℓ)
    (hx : ∀ Q ∈ B, ∀ y ∈ blockSites (ℓ := ℓ) s m Q,
      (freezeRadius d ν β a (aQ Q) : ℝ) ≤ torusDist d ℓ x y) :
    Real.sqrt β * |∑ Q ∈ B, coreMean ν s w B Q x| ≤ 1 / (2 * Real.log (β * a)) := by
  set q := kwQ d ν with hqdef
  have hq0 : 0 < q := kwQ_pos hd hν
  have hq1 : q < 1 := kwQ_lt_one hν
  set S := shellSum d q with hS
  have hSpos : 0 < S := shellSum_pos hq0.le hq1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set C := cL d ν with hC
  have hCdef : C = 4 * d * S / (ν * q) := rfl
  have hCpos : 0 < C := by rw [hCdef]; positivity
  set B' := B.filter fun Q => (blockSites (ℓ := ℓ) s m Q).Nonempty with hB'
  -- reduce to blocks with sites
  have hred : ∑ Q ∈ B, coreMean ν s w B Q x = ∑ Q ∈ B', coreMean ν s w B Q x := by
    rw [hB', Finset.sum_filter_of_ne]
    intro Q _ hne
    by_contra hQ
    apply hne
    simp [coreMean, coreSource_eq_zero_of_empty w B hQ]
  -- per-block bound
  have hper : ∀ Q ∈ B', Real.sqrt β * |coreMean ν s w B Q x| ≤
      2 * d / (ν * q) / (C * Real.log (β * a)) * q ^ ((blockDist s x Q : ℝ) / 2) := by
    intro Q hQ
    rw [hB', Finset.mem_filter] at hQ
    obtain ⟨hQB, hne⟩ := hQ
    obtain ⟨y, hy, hyd⟩ := exists_blockDist x hne
    have hR : freezeRadius d ν β a (aQ Q) ≤ blockDist s x Q := by
      have := hx Q hQB y hy
      rw [torusDist_eq_natCast, hyd] at this
      exact_mod_cast this
    have h3 := freezeRadius_bound hd hν (haQ Q hQB) hlog _ hR
    have h1 := coreMean_bound_q hd hν le_rfl (haQ Q hQB) (hw Q hQB) x
    set n := blockDist s x Q
    have hsq : Real.sqrt β ≥ 0 := Real.sqrt_nonneg β
    have hmid : 0 ≤ 2 * (d : ℝ) / (ν * q) := by positivity
    calc Real.sqrt β * |coreMean ν s w B Q x|
        ≤ Real.sqrt β * (2 * d / (ν * q) * aQ Q * q ^ n) := mul_le_mul_of_nonneg_left h1 hsq
      _ = 2 * d / (ν * q) * (Real.sqrt β * aQ Q * q ^ ((n : ℝ) / 2)) * q ^ ((n : ℝ) / 2) := by
          rw [← rpow_half_mul_self hq0 n]; ring
      _ ≤ 2 * d / (ν * q) * (1 / (C * Real.log (β * a))) * q ^ ((n : ℝ) / 2) := by
          gcongr
      _ = _ := by ring
  -- shell sum
  have hsum : ∑ Q ∈ B', q ^ ((blockDist s x Q : ℝ) / 2) ≤ S := by
    rw [Finset.sum_comp (fun r : ℕ => q ^ ((r : ℝ) / 2)) (fun Q => blockDist s x Q)]
    calc ∑ r ∈ B'.image (fun Q => blockDist s x Q),
          (B'.filter fun Q => blockDist s x Q = r).card • q ^ ((r : ℝ) / 2)
        ≤ ∑ r ∈ B'.image (fun Q => blockDist s x Q), (2 * (r : ℝ) + 1) ^ d * q ^ ((r : ℝ) / 2) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have := card_blocks_dist_le (ℓ := ℓ) s x B r
          have h2 : ((2 * r + 1) ^ d : ℕ) = ((2 * (r : ℝ) + 1) ^ d : ℝ) := by push_cast; ring
          rw [← h2]; exact_mod_cast this
      _ ≤ S := (shell_summable hq0.le hq1).sum_le_tsum _ (fun r _ => by positivity)
  calc Real.sqrt β * |∑ Q ∈ B, coreMean ν s w B Q x|
      = Real.sqrt β * |∑ Q ∈ B', coreMean ν s w B Q x| := by rw [hred]
    _ ≤ Real.sqrt β * ∑ Q ∈ B', |coreMean ν s w B Q x| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Real.sqrt_nonneg β)
    _ = ∑ Q ∈ B', Real.sqrt β * |coreMean ν s w B Q x| := Finset.mul_sum _ _ _
    _ ≤ ∑ Q ∈ B', 2 * d / (ν * q) / (C * Real.log (β * a)) * q ^ ((blockDist s x Q : ℝ) / 2) :=
        Finset.sum_le_sum hper
    _ = 2 * d / (ν * q) / (C * Real.log (β * a)) * ∑ Q ∈ B', q ^ ((blockDist s x Q : ℝ) / 2) := by
        rw [← Finset.mul_sum]
    _ ≤ 2 * d / (ν * q) / (C * Real.log (β * a)) * S :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 / (2 * Real.log (β * a)) := by
        rw [hCdef]; field_simp; norm_num

/-! ### T5: an instance -/

/-- **Non-vacuity.**  `d = 3`, a torus of side `2` with blocks of side `1` (so `m = ℓ = 2`), one bad
block `Q₀ = 0`, bond amplitudes `1`, `a_Q = 1`, `β = 1`, `ν = 1`, and `βa = e^ε` with
`ε = 1/(C_L + 1)`: then `C_L √β a_Q log(βa) < 1`, the frozen radius is `0`, the site
`x = (1, 1, 1)` lies outside the hole, all hypotheses of `mean_outside_collars` hold at `x`, and
the conclusion is stated. -/
theorem mean_outside_collars_instance :
    ∃ (ε : ℝ) (x : Torus 3 2), 0 < ε ∧ 0 < Real.log (1 * Real.exp ε) ∧
      x ∉ siteUnion (ℓ := 2) 1 2 ({fun _ => 0} : Finset (Torus 3 2)) ∧
      freezeRadius 3 1 1 (Real.exp ε) 1 = 0 ∧
      Real.sqrt 1 * |∑ Q ∈ ({fun _ => 0} : Finset (Torus 3 2)),
        coreMean (ℓ := 2) 1 1 (fun _ _ => (1 : ℝ)) {fun _ => 0} Q x| ≤
        1 / (2 * Real.log (1 * Real.exp ε)) := by
  have hC := cL_pos (by norm_num : 0 < 3) (by norm_num : (0 : ℝ) < 1)
  set C := cL 3 1 with hCdef
  set ε : ℝ := 1 / (C + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hlog : Real.log (1 * Real.exp ε) = ε := by simp
  have hrad : freezeRadius 3 1 1 (Real.exp ε) 1 = 0 := by
    unfold freezeRadius
    have h1 : C * Real.sqrt 1 * 1 * Real.log (1 * Real.exp ε) < 1 := by
      rw [hlog, hε]; simp only [Real.sqrt_one, mul_one]
      rw [← div_eq_mul_one_div, div_lt_one (by positivity)]; linarith
    have h2 : 0 < C * Real.sqrt 1 * 1 * Real.log (1 * Real.exp ε) := by
      rw [hlog]; simp only [Real.sqrt_one]; positivity
    have h3 := Real.log_neg h2 h1
    rw [← hCdef, max_eq_right h3.le, mul_zero]
    simp
  have hx : (fun _ : Fin 3 => (1 : ZMod 2)) ∉ siteUnion (ℓ := 2) 1 2
      ({fun _ => 0} : Finset (Torus 3 2)) := by
    intro h
    simp only [siteUnion, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at h
    have := congrFun h 0
    simp [blockMap, blockCoord] at this
  refine ⟨ε, fun _ => 1, hε0, by rw [hlog]; exact hε0, hx, hrad, ?_⟩
  refine mean_outside_collars (ℓ := 2) (m := 2) (by norm_num : 0 < 3) (by norm_num : (0 : ℝ) < 1)
    (by rw [hlog]; exact hε0) (aQ := fun _ => 1) (fun _ _ => zero_le_one)
    (fun _ _ _ _ _ _ => by simp) _ ?_
  intro Q _ y _
  rw [hrad]
  simpa using torusDist_nonneg' (fun _ : Fin 3 => (1 : ZMod 2)) y

end Balaban.LargeField
