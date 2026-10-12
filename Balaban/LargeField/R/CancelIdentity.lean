/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CancelDef
public import Balaban.LargeField.R.ActionConvIdentity
public import Balaban.LargeField.R.WindowGenCompose
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Lemma III.6.3: the cancellation identity (LF-RECONSTRUCTION §III.6.2, (2.53)-(2.58′); P7 pp. 509-511)

The exact identity (2.58′) between the main action of the window with the actual multiscale background
`φ_{k₁,k}(ψ̃)` and the single-scale main action at `(ψ⁰_k, φ⁰_k)`, with the composed Gaussian of
(III.1.4), as an algebraic statement about the landed action functionals.

* `cancel_expansion` ((2.53), P5 (2.23)): the regional conversion identity (`actionRegion_conversion`)
  with `b = e = 0` in the massless branch, in the form
  `A(ψ̃, φ) = A(ψ⁰, φ⁰) + ⟨δψ, a(ψ⁰ - Qφ⁰)⟩ + δA* + ν⟨δφ, φ⁰ - h⟩ + S_st`;
* `sum_P_block`, `sum_block_block`, `sum_mean_block`: the block sums of (2.54), (2.56)-(2.57) via (C1)
  (`compWeight_C1`) and the partition of a `k`-block into leaves;
* `gauss_block_alg`: the expansion of the composed Gaussian (the polynomial identity with `R_η`, `R_s`);
* `cancel_core`: the identity (2.58′) for abstract data;
* `cancellation_identity`: (2.58′) for the window of Definition III.6.1 (`windowData`, `phiZero`), with
  the Euler-Lagrange system of `ψ⁰_{k₁,k}` derived from I-2 (`isEL_phiZero_window`).

The remainder is `Cnat = C^♮ = ∑_z (R_{η,z} + R_{s,z}) - (N/2) ∑_z log(a^♮_z/a_z)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.ActionConv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.LargeField Finset

section Blocks

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- The bilinear dot product on `ℂ^N`. -/
def dotC (u v : Fin N → ℂ) : ℂ := ∑ i, u i * v i

/-- The `k`-block average `V⁻¹ ∑_{x ∈ z} f(x)`. -/
noncomputable def kAvg (f : Torus d (N₀ * L ^ k) → Fin N → ℂ) (z : Torus d (N₀ * L ^ (k - k)))
    (i : Fin N) : ℂ :=
  ((blockVol d L k : ℝ)⁻¹ : ℂ) * ∑ x ∈ fib d L N₀ k k z, f x i

theorem fib_pairwiseDisjoint (S : Finset (Torus d (N₀ * L ^ (k - k)))) :
    (S : Set (Torus d (N₀ * L ^ (k - k)))).PairwiseDisjoint (fib d L N₀ k k) := by
  intro z _ z' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx hx'
  exact hne ((mem_fib.1 hx).symm.trans (mem_fib.1 hx'))

theorem sum_biUnion_fib (S : Finset (Torus d (N₀ * L ^ (k - k))))
    (f : Torus d (N₀ * L ^ k) → ℂ) :
    ∑ x ∈ S.biUnion (fib d L N₀ k k), f x = ∑ z ∈ S, ∑ x ∈ fib d L N₀ k k z, f x :=
  Finset.sum_biUnion (fib_pairwiseDisjoint S)

theorem blk_eq_fib (j : ℕ) (x : Torus d (N₀ * L ^ k)) :
    G.blk j x = fib d L N₀ k j (blkMap d L N₀ k j x) := by
  ext y
  rw [GeneratingSet.mem_blk, mem_fib]
  rfl

theorem leaf_eq_blk (x : Torus d (N₀ * L ^ k)) : leaf G x = G.blk (G.layerIndex x) x := by
  rw [blk_eq_fib]; rfl

theorem blockUnion_sites_layer (D : Region G) {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k) :
    IsBlockUnion L N₀ k n (D.sites ∩ G.layer n) := by
  have key : ∀ x x' : Torus d (N₀ * L ^ k), jBlock d L N₀ k n x = jBlock d L N₀ k n x' →
      x ∈ D.sites ∩ G.layer n → x' ∈ D.sites ∩ G.layer n := by
    intro x x' hjb hx
    obtain ⟨hxD, hxl⟩ := Finset.mem_inter.1 hx
    refine Finset.mem_inter.2 ⟨?_, (G.mem_layer_iff hn1 hnk hjb).1 hxl⟩
    have hn : G.layerIndex x = n := G.layerIndex_eq hn1 hnk hxl
    refine D.blockClosed x hxD x' ?_
    rw [hn]
    exact GeneratingSet.mem_blk.2 hjb.symm
  intro x x' hjb
  exact ⟨key x x' hjb, key x' x hjb.symm⟩

theorem sum_blockAvg_fib (D : Region G) {z : Torus d (N₀ * L ^ (k - k))}
    (hz : fib d L N₀ k k z ⊆ D.sites) (φ : G.Ω 1 × Fin N → ℂ) (i : Fin N) :
    ∑ x ∈ fib d L N₀ k k z, blockAvg G φ x i = ∑ y ∈ fib d L N₀ k k z, svec G φ y i := by
  have hX : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (D.sites ∩ G.layer n) :=
    fun n h1 h2 => blockUnion_sites_layer D h1 h2
  have ha : ∀ s ∈ fib d L N₀ k k z, s ∈ leaf G s := fun s _ => mem_leaf_self G s
  have hb : ∀ s ∈ fib d L N₀ k k z, ∀ s' ∈ leaf G s,
      s' ∈ fib d L N₀ k k z ∧ leaf G s' = leaf G s := by
    intro s hs s' hs'
    obtain ⟨-, -, -, hl⟩ := leaf_closed G hX (hz hs) (D.sub_Ω (hz hs)) hs'
    refine ⟨?_, hl⟩
    rw [mem_fib] at hs ⊢
    rw [blkMap_of_mem_leaf G (layerIndex_le G s) le_rfl hs', hs]
  have hpart := sum_partition_avg (fib d L N₀ k k z) (leaf G) ha hb
    (fun y => svec G φ y i)
  rw [← hpart]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold blockAvg
  rw [← leaf_eq_blk, card_leaf, Complex.real_smul]
  push_cast
  rfl

/-- **`r_z = ψ⁰_k(z) - (Q_kφ⁰_k)(z)`** (Definition III.6.1), at a `k`-block `z`. -/
noncomputable def rBlk (G' : GeneratingSet d L N₀ k ϱ') (a : ℕ → ℝ)
    (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (z : Torus d (N₀ * L ^ (k - k))) (i : Fin N) : ℂ :=
  ((ψ0 ⟨k, z⟩ i : ℝ) : ℂ) - kAvg (fun y j => svec G' (phiZero G' a ψ0 h) y j) z i

theorem resZero_eq_rBlk (a : ℕ → ℝ) (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
    (h : Fin N → ℝ) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G'.Ω 1) (hp : G'.layerIndex x = k)
    (i : Fin N) :
    resZero G' a ψ0 h x i = rBlk G' a ψ0 h (jBlock d L N₀ k k x) i := by
  have hd : x ∈ dataSites G' := (mem_dataSites G').2 (Or.inl hx)
  unfold resZero rBlk
  have e1 : (psiZeroData G' ψ0 h).Ψ x i = ((ψ0 ⟨k, jBlock d L N₀ k k x⟩ i : ℝ) : ℂ) := by
    unfold psiZeroData
    rw [liftSingle_Ψ G' _ _ hd]
  rw [e1]
  unfold blockAvg kAvg
  rw [hp, blk_eq_fib]
  unfold blockVol
  push_cast
  rfl

section C1

variable (G) in
/-- The multiplier `(a_p/a_n) L^{2(n-p)}` of BG (6.2) at a site, with `p = k`. -/
noncomputable def cfk (a : ℕ → ℝ) (x : Torus d (N₀ * L ^ k)) : ℝ :=
  a k / a (G.layerIndex x) * (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ k) ^ 2)

variable (G)

theorem sum_cfk {a₁ : ℝ} (hL : 2 ≤ L) {z : Torus d (N₀ * L ^ (k - k))}
    (hn : ∀ x ∈ fib d L N₀ k k z, 1 ≤ G.layerIndex x ∧ G.layerIndex x < k) :
    ∑ x ∈ fib d L N₀ k k z, cfk G (compWeight L a₁) x =
      compWeight L a₁ k * (blockVol d L k * (compWeight L a₁ k)⁻¹ -
        blockVol d L k * (compWeightZ G a₁ z)⁻¹) := by
  have hVcard : ((fib d L N₀ k k z).card : ℝ) = blockVol d L k := by
    rw [card_fib le_rfl, blockVol_eq]; push_cast; rfl
  have hVpos : 0 < blockVol d L k := by
    unfold blockVol
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hz : (compWeightZ G a₁ z)⁻¹ = (blockVol d L k)⁻¹ *
      ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹ := by
    unfold compWeightZ; rw [inv_inv]
  have e : ∀ x ∈ fib d L N₀ k k z, cfk G (compWeight L a₁) x =
      compWeight L a₁ k * ((compWeight L a₁ k)⁻¹ - (compWeight L a₁ (k - G.layerIndex x))⁻¹) := by
    intro x hx
    rw [← compWeight_C1 (L := L) a₁ (n := G.layerIndex x) (p := k) (hn x hx).2.le]
    unfold cfk
    ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, hVcard, hz]
  have : blockVol d L k * ((blockVol d L k)⁻¹ *
      ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹) =
      ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹ := by
    field_simp
  rw [mul_sub, this]
  ring

theorem sum_cfk_sq {a₁ : ℝ} (ha₁ : 0 < a₁) (hL : 2 ≤ L) {z : Torus d (N₀ * L ^ (k - k))}
    (hn : ∀ x ∈ fib d L N₀ k k z, 1 ≤ G.layerIndex x ∧ G.layerIndex x < k) :
    ∑ x ∈ fib d L N₀ k k z, (compWeight L a₁ (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2) *
        cfk G (compWeight L a₁) x ^ 2 =
      compWeight L a₁ k ^ 2 / ((L : ℝ) ^ k) ^ 2 * (blockVol d L k * (compWeight L a₁ k)⁻¹ -
        blockVol d L k * (compWeightZ G a₁ z)⁻¹) := by
  have hVcard : ((fib d L N₀ k k z).card : ℝ) = blockVol d L k := by
    rw [card_fib le_rfl, blockVol_eq]; push_cast; rfl
  have hVpos : 0 < blockVol d L k := by
    unfold blockVol
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hz : (compWeightZ G a₁ z)⁻¹ = (blockVol d L k)⁻¹ *
      ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹ := by
    unfold compWeightZ; rw [inv_inv]
  have e : ∀ x ∈ fib d L N₀ k k z,
      (compWeight L a₁ (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2) *
        cfk G (compWeight L a₁) x ^ 2 =
      compWeight L a₁ k ^ 2 / ((L : ℝ) ^ k) ^ 2 *
        ((compWeight L a₁ k)⁻¹ - (compWeight L a₁ (k - G.layerIndex x))⁻¹) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hn x hx
    have hapos : compWeight L a₁ (G.layerIndex x) ≠ 0 := (compWeight_pos hL ha₁ h1).ne'
    rw [← compWeight_C1 (L := L) a₁ (n := G.layerIndex x) (p := k) h2.le]
    unfold cfk
    have : ((L : ℝ) ^ G.layerIndex x) ^ 2 ≠ 0 := by positivity
    have : ((L : ℝ) ^ k) ^ 2 ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, hVcard, hz]
  have : blockVol d L k * ((blockVol d L k)⁻¹ *
      ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹) =
      ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹ := by
    field_simp
  rw [mul_sub, this]
  ring

end C1

section BlockSums

variable {a₁ : ℝ}

/-- The local hypotheses on a `k`-block `z`: its sites lie in the region, in layers `1 ≤ n < k`
of the window generating set. -/
def GoodBlock (D : Region G) (z : Torus d (N₀ * L ^ (k - k))) : Prop :=
  fib d L N₀ k k z ⊆ D.sites ∧ ∀ x ∈ fib d L N₀ k k z, 1 ≤ G.layerIndex x ∧ G.layerIndex x < k

theorem blockVol_pos (hL : 0 < L) : 0 < blockVol d L k := by
  unfold blockVol
  have : (0 : ℝ) < L := by exact_mod_cast hL
  positivity

theorem levelCoeff_mul_cfk (hL : 2 ≤ L) (ha₁ : 0 < a₁) {x : Torus d (N₀ * L ^ k)}
    (hn : 1 ≤ G.layerIndex x) :
    levelCoeff G (compWeight L a₁) x * (cfk G (compWeight L a₁) x : ℂ) =
      ((compWeight L a₁ k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) := by
  have hapos : compWeight L a₁ (G.layerIndex x) ≠ 0 := (compWeight_pos hL ha₁ hn).ne'
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  unfold levelCoeff cfk
  rw [← Complex.ofReal_mul]
  congr 1
  have : ((L : ℝ) ^ G.layerIndex x) ^ 2 ≠ 0 := by positivity
  have : ((L : ℝ) ^ k) ^ 2 ≠ 0 := by positivity
  field_simp

theorem sum_P_block (D : Region G) (hL : 2 ≤ L) (ha₁ : 0 < a₁) {z : Torus d (N₀ * L ^ (k - k))}
    (hz : GoodBlock D z) (Dat : BgData G N) (φw : G.Ω 1 × Fin N → ℂ) (rv : Fin N → ℂ)
    (hres : ∀ x ∈ fib d L N₀ k k z, ∀ i, Dat.Ψ x i - blockAvg G φw x i =
      (cfk G (compWeight L a₁) x : ℂ) * rv i) (δ : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    ∑ x ∈ fib d L N₀ k k z, levelCoeff G (compWeight L a₁) x *
        ∑ i, δ x i * (Dat.Ψ x i - blockAvg G φw x i) =
      ((compWeight L a₁ k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k : ℝ) : ℂ) *
        ∑ i, kAvg δ z i * rv i := by
  have hV : (blockVol d L k : ℂ) ≠ 0 := by
    exact_mod_cast (blockVol_pos (by omega : 0 < L)).ne'
  have e : ∀ x ∈ fib d L N₀ k k z, levelCoeff G (compWeight L a₁) x *
        ∑ i, δ x i * (Dat.Ψ x i - blockAvg G φw x i) =
      ((compWeight L a₁ k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) * ∑ i, δ x i * rv i := by
    intro x hx
    have h1 := levelCoeff_mul_cfk (G := G) hL ha₁ (hz.2 x hx).1
    have : ∑ i, δ x i * (Dat.Ψ x i - blockAvg G φw x i) =
        (cfk G (compWeight L a₁) x : ℂ) * ∑ i, δ x i * rv i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hres x hx i]; ring
    rw [this, ← mul_assoc, h1]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  have : ∑ x ∈ fib d L N₀ k k z, ∑ i, δ x i * rv i =
      (blockVol d L k : ℂ) * ∑ i, kAvg δ z i * rv i := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold kAvg
    rw [← Finset.sum_mul]
    field_simp
  rw [this, ← mul_assoc, ← Complex.ofReal_mul]

theorem sum_block_block (D : Region G) (hL : 2 ≤ L) (ha₁ : 0 < a₁) {z : Torus d (N₀ * L ^ (k - k))}
    (hz : GoodBlock D z) (Dat : BgData G N) (φw : G.Ω 1 × Fin N → ℂ) (rv : Fin N → ℂ)
    (hres : ∀ x ∈ fib d L N₀ k k z, ∀ i, Dat.Ψ x i - blockAvg G φw x i =
      (cfk G (compWeight L a₁) x : ℂ) * rv i) :
    ∑ x ∈ fib d L N₀ k k z, levelCoeff G (compWeight L a₁) x *
        ∑ i, (Dat.Ψ x i - blockAvg G φw x i) * (Dat.Ψ x i - blockAvg G φw x i) =
      ((compWeight L a₁ k ^ 2 / ((L : ℝ) ^ k) ^ 2 *
        (blockVol d L k * (compWeight L a₁ k)⁻¹ - blockVol d L k * (compWeightZ G a₁ z)⁻¹) : ℝ) : ℂ) *
        ∑ i, rv i * rv i := by
  have key := sum_cfk_sq G ha₁ hL hz.2
  have e : ∀ x ∈ fib d L N₀ k k z, levelCoeff G (compWeight L a₁) x *
        ∑ i, (Dat.Ψ x i - blockAvg G φw x i) * (Dat.Ψ x i - blockAvg G φw x i) =
      (((compWeight L a₁ (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2) *
        cfk G (compWeight L a₁) x ^ 2 : ℝ) : ℂ) * ∑ i, rv i * rv i := by
    intro x hx
    have : ∑ i, (Dat.Ψ x i - blockAvg G φw x i) * (Dat.Ψ x i - blockAvg G φw x i) =
        ((cfk G (compWeight L a₁) x ^ 2 : ℝ) : ℂ) * ∑ i, rv i * rv i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hres x hx i]; push_cast; ring
    rw [this]
    unfold levelCoeff
    push_cast
    ring
  rw [Finset.sum_congr rfl e, ← Finset.sum_mul, ← Complex.ofReal_sum, key]

theorem sum_mean_block (D : Region G) (hL : 2 ≤ L) {z : Torus d (N₀ * L ^ (k - k))}
    (hz : GoodBlock D z) (Dat : BgData G N) (φw : G.Ω 1 × Fin N → ℂ) (rv : Fin N → ℂ)
    (hres : ∀ x ∈ fib d L N₀ k k z, ∀ i, Dat.Ψ x i - blockAvg G φw x i =
      (cfk G (compWeight L a₁) x : ℂ) * rv i) (i : Fin N) :
    ∑ x ∈ fib d L N₀ k k z, Dat.Ψ x i = ∑ y ∈ fib d L N₀ k k z, svec G φw y i +
      ((compWeight L a₁ k * (blockVol d L k * (compWeight L a₁ k)⁻¹ -
        blockVol d L k * (compWeightZ G a₁ z)⁻¹) : ℝ) : ℂ) * rv i := by
  have key := sum_cfk G (a₁ := a₁) hL hz.2
  have e : ∀ x ∈ fib d L N₀ k k z, Dat.Ψ x i =
      blockAvg G φw x i + (cfk G (compWeight L a₁) x : ℂ) * rv i := by
    intro x hx; rw [← hres x hx i]; ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, sum_blockAvg_fib D hz.1, ← Finset.sum_mul,
    ← Complex.ofReal_sum, key]

end BlockSums

section Union

variable {ϱ₁ ϱ₂ ϱ₃ : ℝ} {G1 : GeneratingSet d L N₀ k ϱ₁} {G2 : GeneratingSet d L N₀ k ϱ₂}
  {G3 : GeneratingSet d L N₀ k ϱ₃}

theorem starWeight_union (A : Region G1) (B : Region G2) (C : Region G3)
    (h : C.sites = A.sites ∪ B.sites) (hd : Disjoint A.sites B.sites) (x : Torus d (N₀ * L ^ k))
    (μ : Fin d) : C.starWeight x μ = A.starWeight x μ + B.starWeight x μ := by
  unfold Region.starWeight
  rw [h]
  have key : ∀ y : Torus d (N₀ * L ^ k), (if y ∈ A.sites ∪ B.sites then (1 : ℝ) else 0) =
      (if y ∈ A.sites then 1 else 0) + (if y ∈ B.sites then 1 else 0) := by
    intro y
    by_cases h1 : y ∈ A.sites
    · have h2 : y ∉ B.sites := fun h2 => Finset.disjoint_left.1 hd h1 h2
      simp [h1, h2]
    · by_cases h2 : y ∈ B.sites <;> simp [h1, h2]
  rw [key x, key (x + Pi.single μ 1)]
  ring

theorem bondPair_union (A : Region G1) (B : Region G2) (C : Region G3)
    (h : C.sites = A.sites ∪ B.sites) (hd : Disjoint A.sites B.sites)
    (f g : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    C.bondPair f g = A.bondPair f g + B.bondPair f g := by
  unfold Region.bondPair
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [starWeight_union A B C h hd]
  push_cast
  ring

theorem massPair_union (A : Region G1) (B : Region G2) (C : Region G3)
    (h : C.sites = A.sites ∪ B.sites) (hd : Disjoint A.sites B.sites)
    (f g : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    C.massPair f g = A.massPair f g + B.massPair f g := by
  unfold Region.massPair
  rw [h, Finset.sum_union hd]

end Union

section Window

variable (hprec : Precedes G G') (a : ℕ → ℝ) (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
  (h : Fin N → ℝ)

theorem windowData_Ψ {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G) :
    (windowData G G' hprec a ψ0 h).Ψ x = psiZeroWin G G' a ψ0 h x := by
  classical
  simp [windowData, BgData.clip, hx]

theorem windowData_h {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    (windowData G G' hprec a ψ0 h).h x = fun i => ((h i : ℝ) : ℂ) := by
  classical
  simp [windowData, BgData.clip, hx]

/-- The extended backgrounds of `𝔹_{k₁,k}` and of `𝔹_k(U_k)` agree on `Ω₁ ∪ C(Ω₁)` of the window
generating set. -/
theorem barField_window_eq {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) (i : Fin N) :
    barField G (windowData G G' hprec a ψ0 h).Ψ (hprec.restrictφ (phiZero G' a ψ0 h)) y i =
      barField G' (psiZeroData G' ψ0 h).Ψ (phiZero G' a ψ0 h) y i := by
  classical
  rcases (mem_dataSites G).1 hy with hy1 | hy1
  · have hy2 : y ∈ G'.Ω 1 := hprec.mem_Ω1 hy1
    have e1 : barField G (windowData G G' hprec a ψ0 h).Ψ (hprec.restrictφ (phiZero G' a ψ0 h)) y i =
        hprec.restrictφ (phiZero G' a ψ0 h) (⟨y, hy1⟩, i) := by simp [barField, hy1]
    have e2 : barField G' (psiZeroData G' ψ0 h).Ψ (phiZero G' a ψ0 h) y i =
        phiZero G' a ψ0 h (⟨y, hy2⟩, i) := by simp [barField, hy2]
    rw [e1, e2]
    rfl
  · have hy2 : y ∉ G.Ω 1 := ((mem_collar G).1 hy1).1
    have e1 : barField G (windowData G G' hprec a ψ0 h).Ψ (hprec.restrictφ (phiZero G' a ψ0 h)) y i =
        (windowData G G' hprec a ψ0 h).Ψ y i := by simp [barField, hy2]
    rw [e1, windowData_Ψ hprec a ψ0 h hy]
    exact composeField_of_collar (G := G) (G' := G') a (phiZero G' a ψ0 h)
      (psiZeroData G' ψ0 h).Ψ hy1 i

theorem svec_window_eq {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.Ω 1) (i : Fin N) :
    svec G (hprec.restrictφ (phiZero G' a ψ0 h)) y i = svec G' (phiZero G' a ψ0 h) y i := by
  have hy2 : y ∈ G'.Ω 1 := hprec.mem_Ω1 hy
  have s1 := svec_of_mem G (hprec.restrictφ (phiZero G' a ψ0 h)) ⟨y, hy⟩ i
  have s2 := svec_of_mem G' (phiZero G' a ψ0 h) ⟨y, hy2⟩ i
  exact s1.trans s2.symm

/-- The bond pairing of a region of the window generating set does not see the difference between the
two extended backgrounds. -/
theorem bondPair_window_eq (D : Region G) :
    D.bondPair (barField G (windowData G G' hprec a ψ0 h).Ψ (hprec.restrictφ (phiZero G' a ψ0 h)))
        (barField G (windowData G G' hprec a ψ0 h).Ψ (hprec.restrictφ (phiZero G' a ψ0 h))) =
      D.bondPair (barField G' (psiZeroData G' ψ0 h).Ψ (phiZero G' a ψ0 h))
        (barField G' (psiZeroData G' ψ0 h).Ψ (phiZero G' a ψ0 h)) := by
  unfold Region.bondPair
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
  by_cases hw : D.starWeight x μ = 0
  · simp [hw]
  · have hx : x ∈ D.sites ∨ x + Pi.single μ 1 ∈ D.sites := by
      by_contra hcon
      push Not at hcon
      apply hw
      unfold Region.starWeight
      simp [hcon.1, hcon.2]
    have hxy : x ∈ dataSites G ∧ x + Pi.single μ 1 ∈ dataSites G := by
      rcases hx with hx | hx
      · have h1 : x ∈ G.Ω 1 := D.sub_Ω hx
        refine ⟨(mem_dataSites G).2 (Or.inl h1), ?_⟩
        by_cases h2 : x + Pi.single μ 1 ∈ G.Ω 1
        · exact (mem_dataSites G).2 (Or.inl h2)
        · exact (mem_dataSites G).2 (Or.inr (mem_collar_of_adj G h1 h2 (adj_add_single x μ)))
      · have h1 : x + Pi.single μ 1 ∈ G.Ω 1 := D.sub_Ω hx
        refine ⟨?_, (mem_dataSites G).2 (Or.inl h1)⟩
        by_cases h2 : x ∈ G.Ω 1
        · exact (mem_dataSites G).2 (Or.inl h2)
        · exact (mem_dataSites G).2 (Or.inr (mem_collar_of_adj G h1 h2 (adj_add_single x μ).symm))
    simp only [barField_window_eq hprec a ψ0 h hxy.1, barField_window_eq hprec a ψ0 h hxy.2]

theorem massPair_window_eq (D : Region G) :
    D.massPair (fun x i => svec G (hprec.restrictφ (phiZero G' a ψ0 h)) x i -
        (windowData G G' hprec a ψ0 h).h x i)
      (fun x i => svec G (hprec.restrictφ (phiZero G' a ψ0 h)) x i -
        (windowData G G' hprec a ψ0 h).h x i) =
      D.massPair (fun x i => svec G' (phiZero G' a ψ0 h) x i - (psiZeroData G' ψ0 h).h x i)
        (fun x i => svec G' (phiZero G' a ψ0 h) x i - (psiZeroData G' ψ0 h).h x i) := by
  unfold Region.massPair
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
  beta_reduce
  have h1 : x ∈ G.Ω 1 := D.sub_Ω hx
  have h2 : x ∈ G'.Ω 1 := hprec.mem_Ω1 h1
  have e1 := windowData_h hprec a ψ0 h h1
  have e2 : (psiZeroData G' ψ0 h).h x = fun i => ((h i : ℝ) : ℂ) := liftSingle_h G' _ _ h2
  rw [svec_window_eq hprec a ψ0 h h1 i, e1, e2]

end Window

section Expansion

variable (D : Region G) (a : ℕ → ℝ) (ν : ℝ) (Dat Du : BgData G N) (φ φu : G.Ω 1 × Fin N → ℂ)
  (α : G.Ω 1 → ℂ)

/-- The linear term `⟨δψ, a (ψ⁰_{k₁,k} - Q φ⁰)⟩_{X_win}` of (2.53). -/
noncomputable def pTerm : ℂ :=
  D.blockPair a (dataInc Dat Du) (fun x i => Dat.Ψ x i - blockAvg G φ x i)

/-- **The fluctuation action `δA*_k(X; δψ, δφ)`** (P5 (2.24)) of the increments `δψ = Ψ̃ - Ψ⁰`,
`δφ = φu - φ`: `½⟨δψ - Qδφ, a(δψ - Qδφ)⟩ + ½‖∂δφ̄‖²_{X*} + ½⟨δφ, α δφ⟩ + (ν/2)‖δφ‖²`. -/
noncomputable def deltaActionC : ℂ :=
  (1 / 2) * D.blockPair a (fun x i => dataInc Dat Du x i - blockAvg G (φu - φ) x i)
      (fun x i => dataInc Dat Du x i - blockAvg G (φu - φ) x i) +
  (1 / 2) * (D.bondPair (wExt Dat Du φ φu) (wExt Dat Du φ φu) +
      D.sitePair α (svec G (φu - φ)) (svec G (φu - φ))) +
  (ν : ℂ) / 2 * D.massPair (svec G (φu - φ)) (svec G (φu - φ))

/-- The `ν`-term `ν⟨δφ, φ⁰ - h⟩_X` of (2.53). -/
noncomputable def nuTerm : ℂ :=
  (ν : ℂ) * D.massPair (svec G (φu - φ)) (fun x i => svec G φ x i - Dat.h x i)

/-- The surface term `S_st = ⟨½[δφ₊ + δφ₋], ∂φ⁰⟩_{st(X)}`. -/
noncomputable def stTerm : ℂ :=
  D.starPair (wExt Dat Du φ φu) (barField G Dat.Ψ φ)

/-- **The main action without block terms** `A*_{0,k}(X; φ)`: `½‖∂φ̄‖²_{X*} + (ν/2)‖φ - h‖²_X`. -/
noncomputable def actionRegion0 : ℂ :=
  (1 / 2) * D.bondPair (barField G Dat.Ψ φ) (barField G Dat.Ψ φ) +
    (ν : ℂ) / 2 * D.massPair (fun x i => svec G φ x i - Dat.h x i)
      (fun x i => svec G φ x i - Dat.h x i)

variable {D a ν Dat Du φ φu α}

/-- **The expansion of the action at a stationary point** (LFR (2.53), P5 (2.23)): the regional
conversion identity with `b = e = 0` in the massless branch.  The base background `(φ, α)` solves the
massless Euler-Lagrange system for `Dat`; `φu` is a hard-spin field. -/
theorem cancel_expansion {β0 : ℝ} (hβ : β0 ≠ 0) (hh : ∀ x i, Du.h x i = Dat.h x i)
    (hEL : IsEL G a 0 Dat φ α) (hφu : ∀ x : G.Ω 1, ∑ i, φu (x, i) * φu (x, i) = 1) :
    (β0 : ℂ) * actionRegionC D a ν Du φu =
      (β0 : ℂ) * actionRegionC D a ν Dat φ +
        (β0 : ℂ) * (pTerm D a Dat Du φ + deltaActionC D a ν Dat Du φ φu α + nuTerm D ν Dat φ φu +
          stTerm D Dat Du φ φu) := by
  have h := actionRegion_conversion (G := G) D MassBranch.massless (a := a) (au := a) (ν := ν)
    (νu := ν) (β := β0) (b := 0) (e := 0) (Dat := Dat) (Du := Du) (φ := φ) (φu := φu) (α := α)
    hβ (fun n => by ring) (by ring) hh hEL hφu
  unfold counterC counterP counterQ counterR at h
  unfold pTerm deltaActionC nuTerm stTerm
  simp only [MassBranch.ind, add_zero, zero_div, mul_zero, Complex.ofReal_zero, zero_mul, one_mul,
    Complex.ofReal_one, zero_add] at h
  linear_combination h

end Expansion

section Gauss

variable (G) in
/-- **The composed mean `𝒬^♮_z ψ̃`** (III.1.4): `V⁻¹ ∑_{x ∈ z} ϖ_{n_x} ψ̃(x)` for the multiscale field `ψ̃`
(the data `Ψ` of the window generating set). -/
noncomputable def compMeanT (ϖ : ℕ → ℝ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (z : Torus d (N₀ * L ^ (k - k))) (i : Fin N) : ℂ :=
  ((blockVol d L k : ℝ)⁻¹ : ℂ) * ∑ x ∈ fib d L N₀ k k z, (ϖ (G.layerIndex x) : ℂ) * Ψ x i

variable (G) in
/-- **`s_z = ∑_x w_x (ϖ_{n_x} - 1) ψ̃(x)`** (proof of Lemma III.6.3). -/
noncomputable def sBlk (ϖ : ℕ → ℝ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (z : Torus d (N₀ * L ^ (k - k))) (i : Fin N) : ℂ :=
  ((blockVol d L k : ℝ)⁻¹ : ℂ) * ∑ x ∈ fib d L N₀ k k z, ((ϖ (G.layerIndex x) : ℂ) - 1) * Ψ x i

variable (G) in
/-- The exponent `𝒢^♮ = ∑_z ½ β_k a^♮_z |ψ_k(z) - 𝒬^♮_z ψ̃|²` of the composed kernel (III.1.4) over the
`k`-blocks `z ∈ Zb`, with the bilinear square (real and complex domain). -/
noncomputable def gaussNat (ϖ : ℕ → ℝ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (βk : ℝ)
    (aN : Torus d (N₀ * L ^ (k - k)) → ℝ) (ψk : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ)
    (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) : ℂ :=
  ∑ z ∈ Zb, (1 / 2 : ℂ) * (βk : ℂ) * (aN z : ℂ) *
    dotC (fun i => ψk z i - compMeanT G ϖ Ψ z i) (fun i => ψk z i - compMeanT G ϖ Ψ z i)

/-- **`const^♮ = ∏_z (β_k a^♮_z / 2π)^{N/2}`** (III.1.4). -/
noncomputable def constNat (N : ℕ) (βk : ℝ) (aN : Torus d (N₀ * L ^ (k - k)) → ℝ)
    (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) : ℝ :=
  ∏ z ∈ Zb, (βk * aN z / (2 * Real.pi)) ^ ((N : ℝ) / 2)

/-- The coupling `β_k = β^{(k)}_0 L^{k(d-2)}` in terms of the canonical coupling. -/
noncomputable def betaK (d L k : ℕ) (β0 : ℝ) : ℝ := β0 * (L : ℝ) ^ (k * (d - 2))

/-- The first part `R_{η,z}` of the remainder (proof of Lemma III.6.3). -/
noncomputable def Reta (βk ak az aN : ℝ) (r q : Fin N → ℂ) : ℂ :=
  (βk : ℂ) * ((aN / az - 1 : ℝ) : ℂ) * (((ak ^ 2 / (2 * az) : ℝ) : ℂ) * dotC r r - (ak : ℂ) * dotC r q)

/-- The second part `R_{s,z}` of the remainder (proof of Lemma III.6.3). -/
noncomputable def Rs (βk aN : ℝ) (ϱ q s : Fin N → ℂ) : ℂ :=
  (βk : ℂ) * (aN : ℂ) * (-(dotC (fun i => ϱ i - q i) s) + (1 / 2 : ℂ) * dotC s s)

/-- **The block identity of the composed Gaussian** (proof of Lemma III.6.3, "Expansion of the
composed Gaussian"): with `a^♮ = a_z(1+η)`, `ϱ = (a_k/a_z) r`,
`½β a^♮ |ϱ - q - s|² = ½β (a_k²/a_z)|r|² - β a_k r·q + ½β a^♮ |q|² + R_η + R_s`. -/
theorem gauss_block_alg {βk ak az aN : ℝ} (haz : az ≠ 0) (r q s ϱ : Fin N → ℂ)
    (hϱ : ∀ i, ϱ i = ((ak / az : ℝ) : ℂ) * r i) :
    (1 / 2 : ℂ) * (βk : ℂ) * (aN : ℂ) * dotC (fun i => ϱ i - q i - s i) (fun i => ϱ i - q i - s i) =
      (1 / 2 : ℂ) * (βk : ℂ) * ((ak ^ 2 / az : ℝ) : ℂ) * dotC r r -
        (βk : ℂ) * (ak : ℂ) * dotC r q + (1 / 2 : ℂ) * (βk : ℂ) * (aN : ℂ) * dotC q q +
        Reta βk ak az aN r q + Rs βk aN ϱ q s := by
  have hazc : (az : ℂ) ≠ 0 := by exact_mod_cast haz
  have hc : ((aN / az - 1 : ℝ) : ℂ) = (aN : ℂ) / az - 1 := by push_cast; ring
  have hd : ((ak / az : ℝ) : ℂ) = (ak : ℂ) / az := by push_cast; ring
  have he : ((ak ^ 2 / az : ℝ) : ℂ) = (ak : ℂ) ^ 2 / az := by push_cast; ring
  have hf : ((ak ^ 2 / (2 * az) : ℝ) : ℂ) = (ak : ℂ) ^ 2 / (2 * az) := by push_cast; ring
  set c : ℂ := (ak : ℂ) / az with hcdef
  have e1 : dotC (fun i => ϱ i - q i - s i) (fun i => ϱ i - q i - s i) =
      c ^ 2 * dotC r r + dotC q q + dotC s s - 2 * c * dotC r q - 2 * c * dotC r s +
        2 * dotC q s := by
    unfold dotC
    simp only [hϱ, hd, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : dotC (fun i => ϱ i - q i) s = c * dotC r s - dotC q s := by
    unfold dotC
    simp only [hϱ, hd, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : dotC r q = dotC q r := by
    unfold dotC; exact Finset.sum_congr rfl fun i _ => by ring
  unfold Reta Rs
  rw [hc, hf, he, e1, e2]
  have hk : (ak : ℂ) = c * az := by rw [hcdef]; field_simp
  rw [hk]
  field_simp
  ring

/-- The generalized remainder `C^♮ = ∑_z (R_{η,z} + R_{s,z}) - (N/2) ∑_z log(a^♮_z/a_z)` (proof of
Lemma III.6.3; `1 + η_z = a^♮_z/a_z`). -/
noncomputable def CnatGen (N : ℕ) (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) (βk ak : ℝ)
    (az aN : Torus d (N₀ * L ^ (k - k)) → ℝ)
    (r q s ϱ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) : ℂ :=
  ∑ z ∈ Zb, (Reta βk ak (az z) (aN z) (r z) (q z) + Rs βk (aN z) (ϱ z) (q z) (s z)) -
    ((N : ℂ) / 2) * ∑ z ∈ Zb, ((Real.log (aN z / az z) : ℝ) : ℂ)

theorem log_constNat {βk : ℝ} (hβ : 0 < βk) {aN az : Torus d (N₀ * L ^ (k - k)) → ℝ}
    {Zb : Finset (Torus d (N₀ * L ^ (k - k)))} (haN : ∀ z ∈ Zb, 0 < aN z)
    (haz : ∀ z ∈ Zb, 0 < az z) :
    Real.log (constNat (d := d) (L := L) (N₀ := N₀) (k := k) N βk aN Zb) -
      Real.log (constNat (d := d) (L := L) (N₀ := N₀) (k := k) N βk az Zb) =
      (N : ℝ) / 2 * ∑ z ∈ Zb, Real.log (aN z / az z) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have h1 : ∀ z ∈ Zb, (βk * aN z / (2 * Real.pi)) ^ ((N : ℝ) / 2) ≠ 0 := fun z hz =>
    (Real.rpow_pos_of_pos (by have := haN z hz; positivity) _).ne'
  have h2 : ∀ z ∈ Zb, (βk * az z / (2 * Real.pi)) ^ ((N : ℝ) / 2) ≠ 0 := fun z hz =>
    (Real.rpow_pos_of_pos (by have := haz z hz; positivity) _).ne'
  unfold constNat
  rw [Real.log_prod h1, Real.log_prod h2, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have ha := haN z hz
  have hb := haz z hz
  rw [Real.log_rpow (by positivity), Real.log_rpow (by positivity), ← mul_sub,
    ← Real.log_div (by positivity) (by positivity)]
  congr 2
  field_simp

theorem compWeightZ_pos {a₁ : ℝ} (ha₁ : 0 < a₁) (hL : 2 ≤ L) (G : GeneratingSet d L N₀ k ϱ)
    {z : Torus d (N₀ * L ^ (k - k))}
    (hn : ∀ x ∈ fib d L N₀ k k z, 1 ≤ G.layerIndex x ∧ G.layerIndex x < k) :
    0 < compWeightZ G a₁ z := by
  unfold compWeightZ
  have hne : (fib d L N₀ k k z).Nonempty := fib_nonempty le_rfl z
  have hV := blockVol_pos (d := d) (k := k) (by omega : 0 < L)
  refine inv_pos.2 (mul_pos (inv_pos.2 hV) (Finset.sum_pos (fun x hx => ?_) hne))
  exact inv_pos.2 (compWeight_pos hL ha₁ (by have := hn x hx; omega))

theorem blockVol_eq_pow (hd : 2 ≤ d) :
    blockVol d L k = (L : ℝ) ^ (k * (d - 2)) * ((L : ℝ) ^ k) ^ 2 := by
  unfold blockVol
  rw [← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

end Gauss

section Site

variable (hprec : Precedes G G') (a : ℕ → ℝ) (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
  (h : Fin N → ℝ)

/-- BG (6.2) at a site whose layer in `𝔹_k(U_k)` is `k`: `ψ⁰_{k₁,k}(x) - Q φ⁰(x) = cfk · r_z`. -/
theorem window_res_site {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hp : G'.layerIndex x = k)
    (i : Fin N) :
    (windowData G G' hprec a ψ0 h).Ψ x i -
        blockAvg G (hprec.restrictφ (phiZero G' a ψ0 h)) x i =
      (cfk G a x : ℂ) * rBlk G' a ψ0 h (jBlock d L N₀ k k x) i := by
  have hd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
  rw [windowData_Ψ hprec a ψ0 h hd, psiZeroWin_sub_blockAvg hprec a ψ0 h hx i,
    resZero_eq_rBlk a ψ0 h (hprec.mem_Ω1 hx) hp i, hp]
  rfl

theorem sum_block_single {z : Torus d (N₀ * L ^ (k - k))}
    (hp : ∀ x ∈ fib d L N₀ k k z, G'.layerIndex x = k)
    (hx : ∀ x ∈ fib d L N₀ k k z, x ∈ G'.Ω 1) :
    ∑ x ∈ fib d L N₀ k k z, levelCoeff G' a x *
        ∑ i, resZero G' a ψ0 h x i * resZero G' a ψ0 h x i =
      ((a k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k : ℝ) : ℂ) *
        ∑ i, rBlk G' a ψ0 h z i * rBlk G' a ψ0 h z i := by
  have e : ∀ x ∈ fib d L N₀ k k z, levelCoeff G' a x *
        ∑ i, resZero G' a ψ0 h x i * resZero G' a ψ0 h x i =
      ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) * ∑ i, rBlk G' a ψ0 h z i * rBlk G' a ψ0 h z i := by
    intro x hxz
    have hz : jBlock d L N₀ k k x = z := mem_fib.1 hxz
    have : ∀ i, resZero G' a ψ0 h x i = rBlk G' a ψ0 h z i := fun i => by
      rw [resZero_eq_rBlk a ψ0 h (hx x hxz) (hp x hxz) i, hz]
    simp only [this]
    unfold levelCoeff
    rw [hp x hxz]
  rw [Finset.sum_congr rfl e, Finset.sum_const, card_fib le_rfl, nsmul_eq_mul]
  have : (((L ^ k) ^ d : ℕ) : ℂ) = ((blockVol d L k : ℝ) : ℂ) := by
    rw [blockVol_eq]; push_cast; rfl
  rw [this]
  push_cast
  ring

end Site

section Core

variable {a₁ : ℝ}

/-- **The algebraic core of the cancellation identity** (LFR Lemma III.6.3, (2.58′)), in terms of abstract
data: `Dat`, `φw` the base data and background of the window `𝔹_{k₁,k}`, `Dp`, `φp` those of
`𝔹_k(U_k)`, `rb = r` the residual of Definition III.6.1, `ψk` the scale-`k` field.  All
hypotheses are the typing/geometry data of the window (the partition `X_win = D₀ ⊔ D_ω ⊔ ⋃_z z` into the
part in `Z_0`, the part in `Ω_k`, and the `k`-blocks of `Z^c_0 ∩ Ω_k^c`) and the identification of the two
backgrounds; no step of the proof is assumed. -/
theorem cancel_core (hd : 2 ≤ d) (hL : 2 ≤ L) (hk : 1 ≤ k) (ha₁ : 0 < a₁) {β0 ν : ℝ}
    (hβ0 : 0 < β0) (Dat Du : BgData G N) (Dp : BgData G' N)
    {φw φu : G.Ω 1 × Fin N → ℂ} {φp : G'.Ω 1 × Fin N → ℂ} {α αu : G.Ω 1 → ℂ}
    (hDuh : ∀ x i, Du.h x i = Dat.h x i) (hELD : IsEL G (compWeight L a₁) 0 Dat φw α)
    (hELu : IsEL G (compWeight L a₁) 0 Du φu αu)
    (D : Region G) (Zr Zk1 : Region G') (D0 Dω : Finset (Torus d (N₀ * L ^ k)))
    (Zb : Finset (Torus d (N₀ * L ^ (k - k))))
    (hD : D.sites = D0 ∪ Dω ∪ Zb.biUnion (fib d L N₀ k k)) (hD0ω : Disjoint D0 Dω)
    (hDr : Disjoint (D0 ∪ Dω) (Zb.biUnion (fib d L N₀ k k)))
    (hZr : Zr.sites = D.sites ∪ Zk1.sites) (hZd : Disjoint D.sites Zk1.sites)
    (hlay' : ∀ x ∈ Zr.sites, G'.layerIndex x = k)
    (rb : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ)
    (hsite : ∀ x ∈ D.sites, ∀ i, Dat.Ψ x i - blockAvg G φw x i =
      (cfk G (compWeight L a₁) x : ℂ) * rb (jBlock d L N₀ k k x) i)
    (hsite' : ∀ x ∈ Zr.sites, ∀ i, Dp.Ψ x i - blockAvg G' φp x i = rb (jBlock d L N₀ k k x) i)
    (hD0r : ∀ x ∈ D0, ∀ i, rb (jBlock d L N₀ k k x) i = 0)
    (hZk1r : ∀ x ∈ Zk1.sites, ∀ i, rb (jBlock d L N₀ k k x) i = 0)
    (hDω : ∀ x ∈ Dω, G.layerIndex x = k ∧ ∀ i, dataInc Dat Du x i = 0)
    (hZb : ∀ z ∈ Zb, ∀ x ∈ fib d L N₀ k k z, 1 ≤ G.layerIndex x ∧ G.layerIndex x < k)
    (ψk : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ)
    (hψk : ∀ z ∈ Zb, ∀ i, ψk z i = rb z i + kAvg (fun y j => svec G' φp y j) z i)
    (hsvec : ∀ x ∈ D.sites, ∀ i, svec G φw x i = svec G' φp x i)
    (hbond : D.bondPair (barField G Dat.Ψ φw) (barField G Dat.Ψ φw) =
      D.bondPair (barField G' Dp.Ψ φp) (barField G' Dp.Ψ φp))
    (hmass : D.massPair (fun x i => svec G φw x i - Dat.h x i) (fun x i => svec G φw x i - Dat.h x i) =
      D.massPair (fun x i => svec G' φp x i - Dp.h x i) (fun x i => svec G' φp x i - Dp.h x i))
    (ϖ : ℕ → ℝ) (aN : Torus d (N₀ * L ^ (k - k)) → ℝ) (haN : ∀ z ∈ Zb, 0 < aN z) :
    gaussNat G ϖ Du.Ψ (betaK d L k β0) aN ψk Zb + (β0 : ℂ) * actionRegionC D (compWeight L a₁) ν Du φu -
        ((Real.log (constNat N (betaK d L k β0) aN Zb) : ℝ) : ℂ) =
      (β0 : ℂ) * actionRegionC Zr (compWeight L a₁) ν Dp φp - (β0 : ℂ) * actionRegion0 Zk1 ν Dp φp +
        ((betaK d L k β0 : ℝ) * ∑ z ∈ Zb, (1 / 2 : ℂ) * (aN z : ℂ) *
            dotC (kAvg (dataInc Dat Du) z) (kAvg (dataInc Dat Du) z) +
          (β0 : ℂ) * (deltaActionC D (compWeight L a₁) ν Dat Du φw φu α + nuTerm D ν Dat φw φu)) +
        (β0 : ℂ) * stTerm D Dat Du φw φu -
        ((Real.log (constNat N (betaK d L k β0) (compWeightZ G a₁) Zb) : ℝ) : ℂ) +
        CnatGen N Zb (betaK d L k β0) ((compWeight L a₁) k) (compWeightZ G a₁) aN rb
          (fun z => kAvg (dataInc Dat Du) z) (sBlk G ϖ Du.Ψ) (fun z i => ψk z i - kAvg Dat.Ψ z i) := by
  classical
  have hak : compWeight L a₁ k ≠ 0 := (compWeight_pos hL ha₁ hk).ne'
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hV : 0 < blockVol d L k := blockVol_pos (by omega)
  have hVeq := blockVol_eq_pow (d := d) (L := L) (k := k) hd
  have hLk2 : ((L : ℝ) ^ k) ^ 2 ≠ 0 := by positivity
  have hβk : 0 < betaK d L k β0 := by unfold betaK; positivity
  have hDZr : D.sites ⊆ Zr.sites := by rw [hZr]; exact Finset.subset_union_left
  have hfibD : ∀ z ∈ Zb, fib d L N₀ k k z ⊆ D.sites := fun z hz x hx => by
    rw [hD]; exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨z, hz, hx⟩)
  have hgood : ∀ z ∈ Zb, GoodBlock D z := fun z hz => ⟨hfibD z hz, hZb z hz⟩
  have hD0D : D0 ⊆ D.sites := by rw [hD]; exact fun x hx => by simp [hx]
  have hDωD : Dω ⊆ D.sites := by rw [hD]; exact fun x hx => by simp [hx]
  have hjb : ∀ z, ∀ x ∈ fib d L N₀ k k z, jBlock d L N₀ k k x = z := fun z x hx => mem_fib.1 hx
  have hresz : ∀ z ∈ Zb, ∀ x ∈ fib d L N₀ k k z, ∀ i, Dat.Ψ x i - blockAvg G φw x i =
      (cfk G (compWeight L a₁) x : ℂ) * rb z i := by
    intro z hz x hx i
    rw [hsite x (hfibD z hz hx) i, hjb z x hx]
  have hres' : ∀ z ∈ Zb, ∀ x ∈ fib d L N₀ k k z, ∀ i,
      Dp.Ψ x i - blockAvg G' φp x i = rb z i := by
    intro z hz x hx i
    rw [hsite' x (hDZr (hfibD z hz hx)) i, hjb z x hx]
  -- the three parts of the block pairing over `D`
  have hsplit : ∀ F : Torus d (N₀ * L ^ k) → ℂ, ∑ x ∈ D.sites, F x =
      ∑ x ∈ D0, F x + ∑ x ∈ Dω, F x + ∑ z ∈ Zb, ∑ x ∈ fib d L N₀ k k z, F x := by
    intro F
    rw [hD, Finset.sum_union hDr, Finset.sum_union hD0ω, sum_biUnion_fib]
  have hXD0 : ∀ x ∈ D0, ∀ i, Dat.Ψ x i - blockAvg G φw x i = 0 := fun x hx i => by
    rw [hsite x (hD0D hx) i, hD0r x hx i, mul_zero]
  obtain ⟨Sω, hSω⟩ : ∃ S : ℂ, S = ∑ x ∈ Dω, levelCoeff G' (compWeight L a₁) x *
      ∑ i, (Dp.Ψ x i - blockAvg G' φp x i) * (Dp.Ψ x i - blockAvg G' φp x i) := ⟨_, rfl⟩
  have hblkD : D.blockPair (compWeight L a₁) (fun x i => Dat.Ψ x i - blockAvg G φw x i)
      (fun x i => Dat.Ψ x i - blockAvg G φw x i) =
      Sω + ∑ z ∈ Zb, ((compWeight L a₁ k ^ 2 / ((L : ℝ) ^ k) ^ 2 * (blockVol d L k *
        (compWeight L a₁ k)⁻¹ - blockVol d L k * (compWeightZ G a₁ z)⁻¹) : ℝ) : ℂ) *
        dotC (rb z) (rb z) := by
    unfold Region.blockPair
    beta_reduce
    rw [hsplit]
    have h0 : ∑ x ∈ D0, levelCoeff G (compWeight L a₁) x *
        ∑ i, (Dat.Ψ x i - blockAvg G φw x i) * (Dat.Ψ x i - blockAvg G φw x i) = 0 :=
      Finset.sum_eq_zero fun x hx => by simp [hXD0 x hx]
    have hω : ∑ x ∈ Dω, levelCoeff G (compWeight L a₁) x *
        ∑ i, (Dat.Ψ x i - blockAvg G φw x i) * (Dat.Ψ x i - blockAvg G φw x i) = Sω := by
      rw [hSω]
      refine Finset.sum_congr rfl fun x hx => ?_
      obtain ⟨hn, -⟩ := hDω x hx
      have hxD := hDωD hx
      have hcf : cfk G (compWeight L a₁) x = 1 := by
        unfold cfk; rw [hn]; field_simp
      have e1 : ∀ i, Dat.Ψ x i - blockAvg G φw x i = rb (jBlock d L N₀ k k x) i := fun i => by
        rw [hsite x hxD i, hcf]; simp
      have e2 : ∀ i, Dp.Ψ x i - blockAvg G' φp x i = rb (jBlock d L N₀ k k x) i := fun i =>
        hsite' x (hDZr hxD) i
      have e3 : levelCoeff G (compWeight L a₁) x = levelCoeff G' (compWeight L a₁) x := by
        unfold levelCoeff; rw [hn, hlay' x (hDZr hxD)]
      simp only [e1, e2, e3]
    have hz : ∑ z ∈ Zb, ∑ x ∈ fib d L N₀ k k z, levelCoeff G (compWeight L a₁) x *
        ∑ i, (Dat.Ψ x i - blockAvg G φw x i) * (Dat.Ψ x i - blockAvg G φw x i) =
        ∑ z ∈ Zb, ((compWeight L a₁ k ^ 2 / ((L : ℝ) ^ k) ^ 2 * (blockVol d L k *
          (compWeight L a₁ k)⁻¹ - blockVol d L k * (compWeightZ G a₁ z)⁻¹) : ℝ) : ℂ) *
          dotC (rb z) (rb z) :=
      Finset.sum_congr rfl fun z hz =>
        sum_block_block D hL ha₁ (hgood z hz) Dat φw (rb z) (hresz z hz)
    rw [h0, hω, hz]
    ring
  have hP : pTerm D (compWeight L a₁) Dat Du φw =
      ∑ z ∈ Zb, ((compWeight L a₁ k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k : ℝ) : ℂ) *
        dotC (kAvg (dataInc Dat Du) z) (rb z) := by
    unfold pTerm Region.blockPair
    beta_reduce
    rw [hsplit]
    have h0 : ∑ x ∈ D0, levelCoeff G (compWeight L a₁) x *
        ∑ i, dataInc Dat Du x i * (Dat.Ψ x i - blockAvg G φw x i) = 0 :=
      Finset.sum_eq_zero fun x hx => by simp [hXD0 x hx]
    have hω : ∑ x ∈ Dω, levelCoeff G (compWeight L a₁) x *
        ∑ i, dataInc Dat Du x i * (Dat.Ψ x i - blockAvg G φw x i) = 0 :=
      Finset.sum_eq_zero fun x hx => by simp [(hDω x hx).2]
    have hz : ∑ z ∈ Zb, ∑ x ∈ fib d L N₀ k k z, levelCoeff G (compWeight L a₁) x *
        ∑ i, dataInc Dat Du x i * (Dat.Ψ x i - blockAvg G φw x i) =
        ∑ z ∈ Zb, ((compWeight L a₁ k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k : ℝ) : ℂ) *
          dotC (kAvg (dataInc Dat Du) z) (rb z) :=
      Finset.sum_congr rfl fun z hz =>
        sum_P_block D hL ha₁ (hgood z hz) Dat φw (rb z) (hresz z hz) (dataInc Dat Du)
    rw [h0, hω, hz]
    ring
  have hblkZ : Zr.blockPair (compWeight L a₁) (fun x i => Dp.Ψ x i - blockAvg G' φp x i)
      (fun x i => Dp.Ψ x i - blockAvg G' φp x i) =
      Sω + ∑ z ∈ Zb, ((compWeight L a₁ k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k : ℝ) : ℂ) *
        dotC (rb z) (rb z) := by
    unfold Region.blockPair
    beta_reduce
    rw [hZr, Finset.sum_union hZd, hsplit]
    have hk1 : ∑ x ∈ Zk1.sites, levelCoeff G' (compWeight L a₁) x *
        ∑ i, (Dp.Ψ x i - blockAvg G' φp x i) * (Dp.Ψ x i - blockAvg G' φp x i) = 0 :=
      Finset.sum_eq_zero fun x hx => by
        have hxZ : x ∈ Zr.sites := by rw [hZr]; exact Finset.mem_union_right _ hx
        have : ∀ i, Dp.Ψ x i - blockAvg G' φp x i = 0 := fun i => by
          rw [hsite' x hxZ i, hZk1r x hx i]
        simp [this]
    have h0 : ∑ x ∈ D0, levelCoeff G' (compWeight L a₁) x *
        ∑ i, (Dp.Ψ x i - blockAvg G' φp x i) * (Dp.Ψ x i - blockAvg G' φp x i) = 0 :=
      Finset.sum_eq_zero fun x hx => by
        have : ∀ i, Dp.Ψ x i - blockAvg G' φp x i = 0 := fun i => by
          rw [hsite' x (hDZr (hD0D hx)) i, hD0r x hx i]
        simp [this]
    have hz : ∀ z ∈ Zb, ∑ x ∈ fib d L N₀ k k z, levelCoeff G' (compWeight L a₁) x *
        ∑ i, (Dp.Ψ x i - blockAvg G' φp x i) * (Dp.Ψ x i - blockAvg G' φp x i) =
        ((compWeight L a₁ k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k : ℝ) : ℂ) *
          dotC (rb z) (rb z) := by
      intro z hz
      have e : ∀ x ∈ fib d L N₀ k k z, levelCoeff G' (compWeight L a₁) x *
          ∑ i, (Dp.Ψ x i - blockAvg G' φp x i) * (Dp.Ψ x i - blockAvg G' φp x i) =
          ((compWeight L a₁ k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) * dotC (rb z) (rb z) := by
        intro x hx
        have hxZ := hDZr (hfibD z hz hx)
        unfold levelCoeff dotC
        simp only [hres' z hz x hx, hlay' x hxZ]
      rw [Finset.sum_congr rfl e, Finset.sum_const, card_fib le_rfl, nsmul_eq_mul]
      have : (((L ^ k) ^ d : ℕ) : ℂ) = ((blockVol d L k : ℝ) : ℂ) := by
        rw [blockVol_eq]; push_cast; rfl
      rw [this]
      push_cast
      ring
    rw [hk1, h0, ← hSω, Finset.sum_congr rfl hz]
    ring
  have hbondZ := bondPair_union D Zk1 Zr hZr hZd (barField G' Dp.Ψ φp) (barField G' Dp.Ψ φp)
  have hmassZ := massPair_union D Zk1 Zr hZr hZd (fun x i => svec G' φp x i - Dp.h x i)
    (fun x i => svec G' φp x i - Dp.h x i)
  -- the block identities
  have hc1 : β0 * (compWeight L a₁ k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k) =
      betaK d L k β0 * compWeight L a₁ k := by
    unfold betaK; rw [hVeq]; field_simp
  have hblock : ∀ z ∈ Zb,
      (1 / 2 : ℂ) * ((betaK d L k β0 : ℝ) : ℂ) * (aN z : ℂ) *
        dotC (fun i => ψk z i - compMeanT G ϖ Du.Ψ z i) (fun i => ψk z i - compMeanT G ϖ Du.Ψ z i) =
      -((1 / 2 : ℂ) * (β0 : ℂ) * (((compWeight L a₁ k ^ 2 / ((L : ℝ) ^ k) ^ 2 * (blockVol d L k *
        (compWeight L a₁ k)⁻¹ - blockVol d L k * (compWeightZ G a₁ z)⁻¹) : ℝ) : ℂ) *
        dotC (rb z) (rb z))) -
      (β0 : ℂ) * (((compWeight L a₁ k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k : ℝ) : ℂ) *
        dotC (kAvg (dataInc Dat Du) z) (rb z)) +
      (1 / 2 : ℂ) * (β0 : ℂ) * (((compWeight L a₁ k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k : ℝ) : ℂ) *
        dotC (rb z) (rb z)) +
      ((betaK d L k β0 : ℝ) : ℂ) * ((1 / 2 : ℂ) * (aN z : ℂ) *
        dotC (kAvg (dataInc Dat Du) z) (kAvg (dataInc Dat Du) z)) +
      (Reta (betaK d L k β0) (compWeight L a₁ k) (compWeightZ G a₁ z) (aN z) (rb z)
          (kAvg (dataInc Dat Du) z) +
        Rs (betaK d L k β0) (aN z) (fun i => ψk z i - kAvg Dat.Ψ z i) (kAvg (dataInc Dat Du) z)
          (sBlk G ϖ Du.Ψ z)) := by
    intro z hz
    have hzg := hgood z hz
    have hazpos : 0 < compWeightZ G a₁ z := compWeightZ_pos ha₁ hL G (hZb z hz)
    have haz : compWeightZ G a₁ z ≠ 0 := hazpos.ne'
    have hVc : (blockVol d L k : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
    have hϱ : ∀ i, ψk z i - kAvg Dat.Ψ z i =
        ((compWeight L a₁ k / compWeightZ G a₁ z : ℝ) : ℂ) * rb z i := by
      intro i
      have hm := sum_mean_block D hL hzg Dat φw (rb z) (hresz z hz) i
      have hs : ∑ y ∈ fib d L N₀ k k z, svec G φw y i = ∑ y ∈ fib d L N₀ k k z, svec G' φp y i :=
        Finset.sum_congr rfl fun y hy => hsvec y (hfibD z hz hy) i
      rw [hs] at hm
      have hkA : kAvg Dat.Ψ z i = kAvg (fun y j => svec G' φp y j) z i +
          ((blockVol d L k : ℝ)⁻¹ : ℂ) * (((compWeight L a₁ k * (blockVol d L k *
            (compWeight L a₁ k)⁻¹ - blockVol d L k * (compWeightZ G a₁ z)⁻¹) : ℝ) : ℂ) * rb z i) := by
        unfold kAvg
        rw [hm]; ring
      rw [hkA, hψk z hz i]
      have hR : 1 - (blockVol d L k)⁻¹ * (compWeight L a₁ k * (blockVol d L k *
          (compWeight L a₁ k)⁻¹ - blockVol d L k * (compWeightZ G a₁ z)⁻¹)) =
          compWeight L a₁ k / compWeightZ G a₁ z := by
        field_simp
        ring
      have hRc : (1 : ℂ) - (((blockVol d L k)⁻¹ * (compWeight L a₁ k * (blockVol d L k *
          (compWeight L a₁ k)⁻¹ - blockVol d L k * (compWeightZ G a₁ z)⁻¹)) : ℝ) : ℂ) =
          ((compWeight L a₁ k / compWeightZ G a₁ z : ℝ) : ℂ) := by
        rw [← hR]; push_cast; ring
      rw [← hRc]
      push_cast
      ring
    have hv : ∀ i, ψk z i - compMeanT G ϖ Du.Ψ z i =
        (ψk z i - kAvg Dat.Ψ z i) - kAvg (dataInc Dat Du) z i - sBlk G ϖ Du.Ψ z i := by
      intro i
      unfold compMeanT sBlk kAvg dataInc
      have : ∑ x ∈ fib d L N₀ k k z, (ϖ (G.layerIndex x) : ℂ) * Du.Ψ x i =
          ∑ x ∈ fib d L N₀ k k z, Dat.Ψ x i + ∑ x ∈ fib d L N₀ k k z, (Du.Ψ x i - Dat.Ψ x i) +
            ∑ x ∈ fib d L N₀ k k z, ((ϖ (G.layerIndex x) : ℂ) - 1) * Du.Ψ x i := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [this]
      ring
    have hgb := gauss_block_alg (βk := betaK d L k β0) (ak := compWeight L a₁ k)
      (az := compWeightZ G a₁ z) (aN := aN z) haz (rb z) (kAvg (dataInc Dat Du) z)
      (sBlk G ϖ Du.Ψ z) (fun i => ψk z i - kAvg Dat.Ψ z i) hϱ
    have hfun : (fun i => ψk z i - compMeanT G ϖ Du.Ψ z i) =
        (fun i => (ψk z i - kAvg Dat.Ψ z i) - kAvg (dataInc Dat Du) z i - sBlk G ϖ Du.Ψ z i) :=
      funext hv
    rw [hfun, hgb]
    have hc2 : β0 * (compWeight L a₁ k ^ 2 / ((L : ℝ) ^ k) ^ 2 * (blockVol d L k *
        (compWeight L a₁ k)⁻¹ - blockVol d L k * (compWeightZ G a₁ z)⁻¹)) =
        betaK d L k β0 * (compWeight L a₁ k - compWeight L a₁ k ^ 2 / compWeightZ G a₁ z) := by
      unfold betaK; rw [hVeq]; field_simp
    have hc1c : (β0 : ℂ) * ((compWeight L a₁ k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k : ℝ) : ℂ) =
        ((betaK d L k β0 : ℝ) : ℂ) * (compWeight L a₁ k : ℂ) := by exact_mod_cast hc1
    have hc2c : (β0 : ℂ) * ((compWeight L a₁ k ^ 2 / ((L : ℝ) ^ k) ^ 2 * (blockVol d L k *
        (compWeight L a₁ k)⁻¹ - blockVol d L k * (compWeightZ G a₁ z)⁻¹) : ℝ) : ℂ) =
        ((betaK d L k β0 : ℝ) : ℂ) * ((compWeight L a₁ k : ℂ) -
          ((compWeight L a₁ k ^ 2 / compWeightZ G a₁ z : ℝ) : ℂ)) := by
      exact_mod_cast hc2
    have hdot : dotC (kAvg (dataInc Dat Du) z) (rb z) = dotC (rb z) (kAvg (dataInc Dat Du) z) := by
      unfold dotC; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hdot]
    linear_combination ((1 / 2 : ℂ) * dotC (rb z) (rb z)) * hc2c +
      (dotC (rb z) (kAvg (dataInc Dat Du) z) - (1 / 2 : ℂ) * dotC (rb z) (rb z)) * hc1c
  have hlog := log_constNat (d := d) (L := L) (N₀ := N₀) (k := k) (N := N) hβk haN
    (az := compWeightZ G a₁) (fun z hz => compWeightZ_pos ha₁ hL G (hZb z hz))
  have hlogc : ((Real.log (constNat N (betaK d L k β0) aN Zb) : ℝ) : ℂ) -
      ((Real.log (constNat N (betaK d L k β0) (compWeightZ G a₁) Zb) : ℝ) : ℂ) =
      ((N : ℂ) / 2) * ∑ z ∈ Zb, ((Real.log (aN z / compWeightZ G a₁ z) : ℝ) : ℂ) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hlog
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_ofNat] at this
    exact this
  have hE := cancel_expansion (D := D) (a := compWeight L a₁) (ν := ν) (Dat := Dat) (Du := Du)
    (φ := φw) (φu := φu) (α := α) hβ0.ne' hDuh hELD (fun x => hELu.2 x)
  have hG' : gaussNat G ϖ Du.Ψ (betaK d L k β0) aN ψk Zb =
      -((1 / 2 : ℂ) * (β0 : ℂ) * ∑ z ∈ Zb, ((compWeight L a₁ k ^ 2 / ((L : ℝ) ^ k) ^ 2 *
          (blockVol d L k * (compWeight L a₁ k)⁻¹ - blockVol d L k * (compWeightZ G a₁ z)⁻¹) : ℝ) : ℂ) *
          dotC (rb z) (rb z)) -
      (β0 : ℂ) * ∑ z ∈ Zb, ((compWeight L a₁ k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k : ℝ) : ℂ) *
        dotC (kAvg (dataInc Dat Du) z) (rb z) +
      (1 / 2 : ℂ) * (β0 : ℂ) * ∑ z ∈ Zb, ((compWeight L a₁ k / ((L : ℝ) ^ k) ^ 2 *
        blockVol d L k : ℝ) : ℂ) * dotC (rb z) (rb z) +
      ((betaK d L k β0 : ℝ) : ℂ) * ∑ z ∈ Zb, (1 / 2 : ℂ) * (aN z : ℂ) *
        dotC (kAvg (dataInc Dat Du) z) (kAvg (dataInc Dat Du) z) +
      ∑ z ∈ Zb, (Reta (betaK d L k β0) (compWeight L a₁ k) (compWeightZ G a₁ z) (aN z) (rb z)
          (kAvg (dataInc Dat Du) z) +
        Rs (betaK d L k β0) (aN z) (fun i => ψk z i - kAvg Dat.Ψ z i) (kAvg (dataInc Dat Du) z)
          (sBlk G ϖ Du.Ψ z)) := by
    unfold gaussNat
    rw [Finset.sum_congr rfl hblock]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← Finset.mul_sum]
  unfold actionRegionC at hE
  unfold actionRegionC actionRegion0 CnatGen
  linear_combination hG' + hE + ((β0 : ℂ) / 2) * hblkD + (β0 : ℂ) * hP - ((β0 : ℂ) / 2) * hblkZ +
    ((β0 : ℂ) / 2) * hbond + ((β0 : ℂ) * ν / 2) * hmass - ((β0 : ℂ) / 2) * hbondZ -
    ((β0 : ℂ) * ν / 2) * hmassZ - hlogc

end Core

section Public

variable (a₁ : ℝ) (hprec : Precedes G G') (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
  (h : Fin N → ℝ)

/-- **`C^♮`** of LFR (2.58′): the remainder of the composition, explicit in the data of the window
(`Reta`, `Rs` and the logarithm of the coefficient error, proof of Lemma III.6.3). -/
noncomputable def Cnat (Du : BgData G N) (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) (β0 : ℝ)
    (ϖ : ℕ → ℝ) (aN : Torus d (N₀ * L ^ (k - k)) → ℝ)
    (ψk : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) : ℂ :=
  CnatGen N Zb (betaK d L k β0) (compWeight L a₁ k) (compWeightZ G a₁) aN
    (rBlk G' (compWeight L a₁) ψ0 h)
    (fun z => kAvg (dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du) z)
    (sBlk G ϖ Du.Ψ)
    (fun z i => ψk z i - kAvg (windowData G G' hprec (compWeight L a₁) ψ0 h).Ψ z i)

/-- **Lemma III.6.3 (the fundamental formula; LFR (2.58′); P7 (2.53)–(2.58))**, algebraic part.

Setting (Definition III.6.1): `G = 𝔹_{k₁,k}` the window generating set, `G' = 𝔹_k(U_k)`, `Dat =
windowData` the datum `ψ⁰_{k₁,k}` of BG (6.2), `φ⁰_k = phiZero`, `Du` the datum `ψ̃` of the window and
`(φu, αu) = φ_{k₁,k}` its massless background (`IsEL`); `D = X_win`, `Zr = Z`, `Zk1 = Z_{k₁}`
(regions of the generating sets); `Zb` the `k`-blocks of `Z^c_0 ∩ Ω^c_k`, `D0 = X_win ∩ Z_0`,
`Dω = X_win ∩ Ω_k`; `β_k = β^{(k)}_0 L^{k(d-2)}` (`betaK`), `a^♮_z = aN z`, `ϖ` the layer factors of the
composed mean.  Then, with `a_z = compWeightZ`,
`𝒢^♮ + β_k A*_k(X_win; ψ, φ_{k₁,k}) - log const^♮ = β_k A*_k(Z; ψ⁰_k, φ⁰_k) - β_k A*_{0,k}(Z_{k₁}; φ⁰_k)
 + β_k{Σ_z ½ a^♮_z |Q_z δψ|² + δA* + ν⟨δφ, φ⁰ - h⟩} + β_k S_st - log const + C^♮`
(in the normalization `β_k A* = β^{(k)}_0 · (site sum)`, so the `Q_zδψ` term carries `β_k`, the
`A*`-terms `β^{(k)}_0`).  The geometry hypotheses are the partition `X_win = D₀ ⊔ D_ω ⊔ ⋃_{z∈Zb} z`,
`Z = X_win ⊔ Z_{k₁}`, the layers (`1 ≤ n < k` on the `k`-blocks of `Zb`, `k` on `Ω_k` and in
`𝔹_k(U_k)`), the vanishing of `r` on `Z_0 ⊇ Z_{k₁}` ((2.52): the stationarity of (2.34)) and
`δψ = 0` on `Ω_k` (Lemma III.4.6); the field `ψ_k` equals `ψ⁰_k` on `Zb`. -/
theorem cancellation_identity {a₁ : ℝ} (hd : 2 ≤ d) (hL : 2 ≤ L) (hk : 1 ≤ k) (ha₁ : 0 < a₁) {β0 ν : ℝ}
    (hβ0 : 0 < β0) (H' : BgHyp d L k ϱ' (compWeight L a₁) 0)
    (hDom : InUnionDomainR G' (bgC1 d L N) 0 (psiZeroData G' ψ0 h))
    (Du : BgData G N) {φu : G.Ω 1 × Fin N → ℂ} {αu : G.Ω 1 → ℂ}
    (hDuh : ∀ x i, Du.h x i = (windowData G G' hprec (compWeight L a₁) ψ0 h).h x i)
    (hELu : IsEL G (compWeight L a₁) 0 Du φu αu)
    (D : Region G) (Zr Zk1 : Region G') (D0 Dω : Finset (Torus d (N₀ * L ^ k)))
    (Zb : Finset (Torus d (N₀ * L ^ (k - k))))
    (hD : D.sites = D0 ∪ Dω ∪ Zb.biUnion (fib d L N₀ k k)) (hD0ω : Disjoint D0 Dω)
    (hDr : Disjoint (D0 ∪ Dω) (Zb.biUnion (fib d L N₀ k k)))
    (hZr : Zr.sites = D.sites ∪ Zk1.sites) (hZd : Disjoint D.sites Zk1.sites)
    (hlay' : ∀ x ∈ Zr.sites, G'.layerIndex x = k)
    (hD0r : ∀ x ∈ D0, ∀ i, rBlk G' (compWeight L a₁) ψ0 h (jBlock d L N₀ k k x) i = 0)
    (hZk1r : ∀ x ∈ Zk1.sites, ∀ i, rBlk G' (compWeight L a₁) ψ0 h (jBlock d L N₀ k k x) i = 0)
    (hDω : ∀ x ∈ Dω, G.layerIndex x = k ∧
      ∀ i, dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du x i = 0)
    (hZb : ∀ z ∈ Zb, ∀ x ∈ fib d L N₀ k k z, 1 ≤ G.layerIndex x ∧ G.layerIndex x < k)
    (ψk : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ)
    (hψk : ∀ z ∈ Zb, ∀ i, ψk z i = ((ψ0 ⟨k, z⟩ i : ℝ) : ℂ))
    (ϖ : ℕ → ℝ) (aN : Torus d (N₀ * L ^ (k - k)) → ℝ) (haN : ∀ z ∈ Zb, 0 < aN z) :
    gaussNat G ϖ Du.Ψ (betaK d L k β0) aN ψk Zb + (β0 : ℂ) * actionRegionC D (compWeight L a₁) ν Du φu -
        ((Real.log (constNat N (betaK d L k β0) aN Zb) : ℝ) : ℂ) =
      (β0 : ℂ) * actionRegionC Zr (compWeight L a₁) ν (psiZeroData G' ψ0 h) (phiZero G' (compWeight L a₁) ψ0 h) -
        (β0 : ℂ) * actionRegion0 Zk1 ν (psiZeroData G' ψ0 h) (phiZero G' (compWeight L a₁) ψ0 h) +
        ((betaK d L k β0 : ℝ) * ∑ z ∈ Zb, (1 / 2 : ℂ) * (aN z : ℂ) *
            dotC (kAvg (dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du) z)
              (kAvg (dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du) z) +
          (β0 : ℂ) * (deltaActionC D (compWeight L a₁) ν (windowData G G' hprec (compWeight L a₁) ψ0 h) Du
              (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu
              (hprec.restrictα (alphaZero G' (compWeight L a₁) ψ0 h)) +
            nuTerm D ν (windowData G G' hprec (compWeight L a₁) ψ0 h)
              (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu)) +
        (β0 : ℂ) * stTerm D (windowData G G' hprec (compWeight L a₁) ψ0 h) Du
          (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu -
        ((Real.log (constNat N (betaK d L k β0) (compWeightZ G a₁) Zb) : ℝ) : ℂ) +
        Cnat a₁ hprec ψ0 h Du Zb β0 ϖ aN ψk := by
  have hha : ∀ j, 1 ≤ j → j ≤ k → compWeight L a₁ j ≠ 0 := fun j hj _ =>
    (compWeight_pos hL ha₁ hj).ne'
  have hELD := isEL_phiZero_window hprec hha H' hDom
  have hDZr : D.sites ⊆ Zr.sites := by rw [hZr]; exact Finset.subset_union_left
  refine cancel_core hd hL hk ha₁ hβ0 (windowData G G' hprec (compWeight L a₁) ψ0 h) Du
    (psiZeroData G' ψ0 h) hDuh hELD hELu D Zr Zk1 D0 Dω Zb hD hD0ω hDr hZr hZd hlay'
    (rBlk G' (compWeight L a₁) ψ0 h) ?_ ?_ hD0r hZk1r hDω hZb ψk ?_ ?_ (bondPair_window_eq hprec _ ψ0 h D)
    (massPair_window_eq hprec _ ψ0 h D) ϖ aN haN
  · intro x hx i
    exact window_res_site hprec _ ψ0 h (D.sub_Ω hx) (hlay' x (hDZr hx)) i
  · intro x hx i
    have h1 : x ∈ G'.Ω 1 := Zr.sub_Ω hx
    have := resZero_eq_rBlk (compWeight L a₁) ψ0 h h1 (hlay' x hx) i
    exact this
  · intro z hz i
    rw [hψk z hz i]
    unfold rBlk
    ring
  · intro x hx i
    exact svec_window_eq hprec _ ψ0 h (D.sub_Ω hx) i

end Public

end Blocks

end Balaban.LargeField.ActionConv
