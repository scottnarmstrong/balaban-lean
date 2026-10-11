/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Calculus
public import Balaban.Background.Contraction
public import Balaban.Background.Data
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Two generating sets: the composed field and the composition identities
(BACKGROUND.md §6.1–§6.4, §6.7; P2 §4)

For generating sets `𝔹_j ≺ 𝔹'_k` on the same torus (`Precedes G G'`) and a field `φ'` on `Ω'₁`
with data `Ψ'` for `𝔹'_k`:

* `Balaban.Background.compWeight`, `compWeight_C1`: the weights (6.1) and the identity (C1);
* `Balaban.Background.composeField`: the explicit function (6.2), defined for *any* `φ'`;
* `Balaban.Background.composeData`: the same as `BgData` of `𝔹_j`;
* `Balaban.Background.isEL_compose` (Theorem 6.1 (ii), (iv), pointwise algebra): if `(φ', α')`
  solves (EL) for `𝔹'_k` with datum `D'`, its restriction to `Ω₁` solves (EL) for `𝔹_j` with the
  datum `composeData`; `isSmallSolution_compose`: the size restriction is inherited;
* `Balaban.Background.prop64`: the perturbed composition (Proposition 6.4, `g ≡ 0`).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-! ### The weights (6.1) and the identity (C1) -/

/-- The weights (6.1) (P2 (4.4)): `a_r = a₁ (1 - L⁻²) / (1 - L⁻²ʳ)`.  For `r = 0` the quotient is
`0` (division by zero), which is the convention `u₀ = 1 / a₀ = 0` of §6.5. -/
noncomputable def compWeight (L : ℕ) (a₁ : ℝ) (r : ℕ) : ℝ :=
  a₁ * (1 - (((L : ℝ) ^ 2)⁻¹)) / (1 - ((((L : ℝ) ^ r) ^ 2)⁻¹))

theorem compWeight_one {L : ℕ} (hL : 2 ≤ L) (a₁ : ℝ) : compWeight L a₁ 1 = a₁ := by
  unfold compWeight
  have h2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have h4 : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hne : (1 - (((L : ℝ) ^ 2)⁻¹)) ≠ 0 := by
    have : ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h4
    linarith
  simp only [pow_one]
  exact mul_div_cancel_right₀ a₁ hne

/-- `u_r = 1 / a_r = (1 - L⁻²ʳ) / (a₁ (1 - L⁻²))`, valid for every `r` (also `r = 0`). -/
theorem compWeight_inv (L : ℕ) (a₁ : ℝ) (r : ℕ) :
    (compWeight L a₁ r)⁻¹ =
      (1 - ((((L : ℝ) ^ r) ^ 2)⁻¹)) / (a₁ * (1 - (((L : ℝ) ^ 2)⁻¹))) := by
  unfold compWeight
  rw [inv_div]

/-- **(C1)** (P2 (4.18)): `L^{2(n-p)} u_n = u_p - u_{p-n}` for `n ≤ p`, `u_r = 1 / a_r`. -/
theorem compWeight_C1 (a₁ : ℝ) {n p : ℕ} (hnp : n ≤ p) :
    ((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ p) ^ 2 * (compWeight L a₁ n)⁻¹ =
      (compWeight L a₁ p)⁻¹ - (compWeight L a₁ (p - n))⁻¹ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnp
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  simp only [compWeight_inv, Nat.add_sub_cancel_left, pow_add]
  field_simp
  ring

/-! ### Two generating sets -/

section Prec

variable (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')

/-- `𝔹_j ≺ 𝔹'_k` (P2 (4.1)): two generating sets on the same torus with `Ω_i ⊆ Ω'_i`.  (`𝔹_j` has
`Ω_i = ∅` for `i > j`; this is not needed for the algebra.) -/
def Precedes : Prop := ∀ i, 1 ≤ i → i ≤ k → G.Ω i ⊆ G'.Ω i

variable {G G'}

theorem one_le_of_mem_Ω1 {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) : 1 ≤ k := by
  by_contra h
  have : k = 0 := by omega
  subst this
  have h0 := G.top
  simp only [zero_add] at h0
  rw [h0] at hx
  exact Finset.notMem_empty _ hx

theorem Precedes.mem_Ω1 (h : Precedes G G') {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    x ∈ G'.Ω 1 :=
  h 1 le_rfl (one_le_of_mem_Ω1 hx) hx

/-- The inclusion `Ω₁ ⊆ Ω'₁` as a map of subtypes. -/
def Precedes.incl (h : Precedes G G') (x : G.Ω 1) : G'.Ω 1 := ⟨x.1, h.mem_Ω1 x.2⟩

@[simp] theorem Precedes.incl_val (h : Precedes G G') (x : G.Ω 1) :
    ((h.incl x : G'.Ω 1) : Torus d (N₀ * L ^ k)) = x := rfl

theorem Precedes.layerIndex_le (h : Precedes G G') {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    G.layerIndex x ≤ G'.layerIndex x := by
  obtain ⟨hn1, hnk, hxn⟩ := G.layerIndex_spec hx
  obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec (h.mem_Ω1 hx)
  by_contra hlt
  push Not at hlt
  have h1 : x ∈ G'.Ω (G.layerIndex x) := h _ hn1 hnk (G.mem_layer.1 hxn).1
  have h2 : x ∈ G'.Ω (G'.layerIndex x + 1) :=
    G'.Ω_antitone (by omega) (by omega) (by omega) h1
  exact (G'.mem_layer.1 hxp).2 h2

/-- The nesting of blocks: a `p`-block contains the `n`-blocks it meets, `n ≤ p ≤ k`. -/
theorem jBlock_eq_of_le {n p : ℕ} (hnp : n ≤ p) (hp : p ≤ k) {x x' : Torus d (N₀ * L ^ k)}
    (h : jBlock d L N₀ k n x = jBlock d L N₀ k n x') :
    jBlock d L N₀ k p x = jBlock d L N₀ k p x' := by
  induction p, hnp using Nat.le_induction with
  | base => exact h
  | succ p hnp ih =>
    exact GeneratingSet.jBlock_succ_eq hp (ih (by omega))

theorem blk_eq_of_mem {j : ℕ} {x x' : Torus d (N₀ * L ^ k)} (h : x' ∈ G.blk j x) :
    G.blk j x' = G.blk j x := by
  ext y
  rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk, GeneratingSet.mem_blk.1 h]

/-- Facts on a site `x'` of the `n`-block of a site `x ∈ Ω₁` (`n = n(x)`), for `𝔹_j ≺ 𝔹'_k`:
the layer index and block of `𝔹_j` and of `𝔹'_k` are constant on it. -/
theorem Precedes.block_compat (h : Precedes G G') {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (hx' : x' ∈ G.blk (G.layerIndex x) x) :
    x' ∈ G.Ω 1 ∧ G.layerIndex x' = G.layerIndex x ∧
      G.blk (G.layerIndex x') x' = G.blk (G.layerIndex x) x ∧
      G'.layerIndex x' = G'.layerIndex x ∧
      G'.blk (G'.layerIndex x') x' = G'.blk (G'.layerIndex x) x := by
  obtain ⟨hn1, hnk, hxn⟩ := G.layerIndex_spec hx
  have hb := GeneratingSet.mem_blk.1 hx'
  have hx'n : x' ∈ G.layer (G.layerIndex x) := (G.mem_layer_iff hn1 hnk hb).2 hxn
  have hx'1 : x' ∈ G.Ω 1 := G.layer_subset hn1 hnk hx'n
  have e1 : G.layerIndex x' = G.layerIndex x := G.layerIndex_eq hn1 hnk hx'n
  obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec (h.mem_Ω1 hx)
  have hnp := h.layerIndex_le hx
  have hbp : jBlock d L N₀ k (G'.layerIndex x) x' = jBlock d L N₀ k (G'.layerIndex x) x :=
    jBlock_eq_of_le hnp hpk hb
  have hx'p : x' ∈ G'.layer (G'.layerIndex x) := (G'.mem_layer_iff hp1 hpk hbp).2 hxp
  have e2 : G'.layerIndex x' = G'.layerIndex x := G'.layerIndex_eq hp1 hpk hx'p
  refine ⟨hx'1, e1, ?_, e2, ?_⟩
  · rw [e1]; exact blk_eq_of_mem hx'
  · rw [e2]; exact blk_eq_of_mem (GeneratingSet.mem_blk.2 hbp)

end Prec

/-! ### The composed field (6.2) -/

section Compose

variable (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')

/-- The block average `L^{-nd} ∑_{y ∈ B_n(x)} w(y)` of a torus function. -/
noncomputable def blockMean {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (n : ℕ)
    (w : Torus d (N₀ * L ^ k) → ℂ) (x : Torus d (N₀ * L ^ k)) : ℂ :=
  ((((((L : ℝ) ^ n) ^ d)⁻¹ : ℝ) : ℂ)) * ∑ y ∈ G.blk n x, w y

/-- **The composed field `Ψ = ψ(𝔹_j, 𝔹'_k; Ψ')`** (6.2), for any `φ'` on `Ω'₁` and any `Ψ'`:
for `x ∈ Ω₁` (`n`, `p` the layers of `𝔹_j`, `𝔹'_k`)
`Ψ(x) = (Q_n φ')(x) + (a_p / a_n) L^{2(n-p)} (Ψ'(x) - (Q_p φ')(x))`, on the collar `C(Ω₁)` the
extension `φ̄'` of `φ'` by `Ψ'`, and `0` elsewhere. -/
noncomputable def composeField (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) (i : Fin N) : ℂ := by
  classical
  exact if x ∈ G.Ω 1 then
      blockMean G (G.layerIndex x) (fun y => svec G' φ' y i) x +
        ((a (G'.layerIndex x) / a (G.layerIndex x) *
          (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) : ℝ) : ℂ) *
          (Ψ' x i - blockMean G' (G'.layerIndex x) (fun y => svec G' φ' y i) x)
    else if x ∈ collar G then barField G' Ψ' φ' x i else 0

variable {G G'}

theorem blockMean_congr {n : ℕ} (w : Torus d (N₀ * L ^ k) → ℂ) {x x' : Torus d (N₀ * L ^ k)}
    (h : G.blk n x' = G.blk n x) : blockMean G n w x' = blockMean G n w x := by
  unfold blockMean
  rw [h]

theorem composeField_of_mem (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (i : Fin N) :
    composeField G G' a φ' Ψ' x i =
      blockMean G (G.layerIndex x) (fun y => svec G' φ' y i) x +
        ((a (G'.layerIndex x) / a (G.layerIndex x) *
          (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) : ℝ) : ℂ) *
          (Ψ' x i - blockMean G' (G'.layerIndex x) (fun y => svec G' φ' y i) x) := by
  simp [composeField, hx]

theorem composeField_of_collar (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ collar G)
    (i : Fin N) :
    composeField G G' a φ' Ψ' x i = barField G' Ψ' φ' x i := by
  have h1 : x ∉ G.Ω 1 := ((mem_collar G).1 hx).1
  simp [composeField, h1, hx]

theorem composeField_of_not_mem (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∉ dataSites G) (i : Fin N) : composeField G G' a φ' Ψ' x i = 0 := by
  have h1 : x ∉ G.Ω 1 := fun h => hx ((mem_dataSites G).2 (Or.inl h))
  have h2 : x ∉ collar G := fun h => hx ((mem_dataSites G).2 (Or.inr h))
  simp [composeField, h1, h2]

/-- The composed field is constant on the blocks of every layer of `𝔹_j`, if `Ψ'` is constant on
the blocks of every layer of `𝔹'_k`. -/
theorem composeField_layerConst (h : Precedes G G') (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hΨ' : IsLayerConstant G' Ψ') :
    IsLayerConstant G (fun x i => composeField G G' a φ' Ψ' x i) := by
  intro n hn1 hnk x hx x' hx'
  have hxΩ : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
  have hn : G.layerIndex x = n := G.layerIndex_eq hn1 hnk hx
  have hx'b : x' ∈ G.blk (G.layerIndex x) x := by rw [hn]; exact hx'
  obtain ⟨hx'1, e1, e2, e3, e4⟩ := h.block_compat hxΩ hx'b
  funext i
  show composeField G G' a φ' Ψ' x' i = composeField G G' a φ' Ψ' x i
  rw [composeField_of_mem a φ' Ψ' hx'1, composeField_of_mem a φ' Ψ' hxΩ, e1, e3]
  rw [e1] at e2
  rw [e3] at e4
  rw [blockMean_congr _ e2, blockMean_congr _ e4]
  -- `Ψ' x' = Ψ' x`
  obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec (h.mem_Ω1 hxΩ)
  have hx'p : x' ∈ G'.blk (G'.layerIndex x) x := by
    have hnp := h.layerIndex_le hxΩ
    have hb := GeneratingSet.mem_blk.1 hx'b
    exact GeneratingSet.mem_blk.2 (jBlock_eq_of_le hnp hpk hb)
  rw [hΨ' _ hp1 hpk x hxp x' hx'p]

/-- **The composed datum** as `BgData` of `𝔹_j`: the field `Ψ` of (6.2) and `h̃` restricted to `Ω₁`. -/
noncomputable def composeData (h : Precedes G G') (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (D' : BgData G' N) : BgData G N where
  Ψ := fun x i => composeField G G' a φ' D'.Ψ x i
  h := fun x i => by classical exact if x ∈ G.Ω 1 then D'.h x i else 0
  Ψ_layerConst := composeField_layerConst h a φ' D'.Ψ_layerConst
  h_layerConst := by
    intro n hn1 hnk x hx x' hx'
    have hxΩ : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
    have hn : G.layerIndex x = n := G.layerIndex_eq hn1 hnk hx
    have hx'b : x' ∈ G.blk (G.layerIndex x) x := by rw [hn]; exact hx'
    obtain ⟨hx'1, -, -, -, -⟩ := h.block_compat hxΩ hx'b
    obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec (h.mem_Ω1 hxΩ)
    have hx'p : x' ∈ G'.blk (G'.layerIndex x) x :=
      GeneratingSet.mem_blk.2 (jBlock_eq_of_le (h.layerIndex_le hxΩ) hpk
        (GeneratingSet.mem_blk.1 hx'b))
    funext i
    simp only [hxΩ, hx'1, ↓reduceIte]
    rw [D'.h_layerConst _ hp1 hpk x hxp x' hx'p]
  Ψ_zero := by
    intro x hx
    funext i
    exact composeField_of_not_mem a φ' D'.Ψ hx i
  h_zero := by
    intro x hx
    funext i
    simp [hx]

end Compose

/-! ### Transfer of the linear equation -/

section Transfer

/-- A neighbour `y` of a site of `Ω₁`: the zero extension plus the collar datum is the extension
`φ̄` by the datum. -/
theorem zeroExt_add_collar (G : GeneratingSet d L N₀ k ϱ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (φ : G.Ω 1 × Fin N → ℂ) (i : Fin N) {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (hxy : Adj x y) :
    zeroExt (G.Ω 1) (fun z => φ (z, i)) y + (if y ∈ collar G then Ψ y i else 0) =
      barField G Ψ φ y i := by
  classical
  by_cases hy : y ∈ G.Ω 1
  · have hc : y ∉ collar G := fun h => ((mem_collar G).1 h).1 hy
    simp [zeroExt_mem _ _ ⟨y, hy⟩, hc, barField, hy]
  · have hc : y ∈ collar G := (mem_collar G).2 ⟨hy, x, hx, hxy⟩
    simp [zeroExt_not_mem _ _ hy, hc, barField, hy]

/-- `(-Δ ũ)(x) - 𝔟(Ψ)(x) = ∑_μ (2 φ(x) - φ̄(x + e_μ) - φ̄(x - e_μ))`. -/
theorem negLap_sub_boundary (G : GeneratingSet d L N₀ k ϱ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (φ : G.Ω 1 × Fin N → ℂ) (i : Fin N) (x : G.Ω 1) :
    negLap (zeroExt (G.Ω 1) (fun z => φ (z, i))) (x : Torus d (N₀ * L ^ k)) -
        boundaryTerm G Ψ (x, i) =
      ∑ μ : Fin d, (2 * φ (x, i) - barField G Ψ φ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
        barField G Ψ φ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i) := by
  classical
  unfold negLap boundaryTerm
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h1 := zeroExt_add_collar G Ψ φ i x.2 (y := (x : Torus d (N₀ * L ^ k)) + Pi.single μ 1)
    ⟨μ, Or.inl rfl⟩
  have h2 := zeroExt_add_collar G Ψ φ i x.2 (y := (x : Torus d (N₀ * L ^ k)) - Pi.single μ 1)
    ⟨μ, Or.inr (by simp)⟩
  rw [zeroExt_mem _ _ x]
  linear_combination (-1 : ℂ) * h1 - h2

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- On `Ω₁ ∪ C(Ω₁)` the extension of `φ'|_{Ω₁}` by the composed field is the extension `φ̄'`. -/
theorem barField_compose (h : Precedes G G') (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ dataSites G) (i : Fin N) :
    barField G (fun z j => composeField G G' a φ' Ψ' z j)
        (fun q => φ' (h.incl q.1, q.2)) y i = barField G' Ψ' φ' y i := by
  classical
  rcases (mem_dataSites G).1 hy with hy | hy
  · have hy' := h.mem_Ω1 hy
    simp [barField, hy, hy']
    rfl
  · have hn : y ∉ G.Ω 1 := ((mem_collar G).1 hy).1
    simp [barField, hn, composeField_of_collar a φ' Ψ' hy]

omit [NeZero N₀] [NeZero L] in
theorem adj_add_single (x : Torus d (N₀ * L ^ k)) (μ : Fin d) : Adj x (x + Pi.single μ 1) :=
  ⟨μ, Or.inl rfl⟩

omit [NeZero N₀] [NeZero L] in
theorem adj_sub_single (x : Torus d (N₀ * L ^ k)) (μ : Fin d) : Adj x (x - Pi.single μ 1) :=
  ⟨μ, Or.inr (by simp)⟩

theorem blockTerm_zeroExt_eq (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (w : Torus d (N₀ * L ^ k) → ℂ)
    (x : Torus d (N₀ * L ^ k)) :
    blockTerm G a w x = ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
      blockMean G (G.layerIndex x) w x := rfl

/-- **Transfer of the linear equation** (the pointwise algebra of §6.4, (6.3)–(6.4), with no use
of the constraint): for `x ∈ Ω₁`, the residual of the `𝔹_j` equation at the composed datum
(without the term `ν h̃`) equals the residual of the `𝔹'_k` equation at `x`. -/
theorem resid_compose (h : Precedes G G') (a : ℕ → ℝ) (ha : ∀ j, 1 ≤ j → j ≤ k → a j ≠ 0)
    (ν : ℝ) (β' : G'.Ω 1 → ℂ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (x : G.Ω 1) (i : Fin N) :
    (liftOp N (dirichletOperator G a ν (fun z => β' (h.incl z))) *ᵥ
        (fun q => φ' (h.incl q.1, q.2))) (x, i) -
      qStar G a (fun z j => composeField G G' a φ' Ψ' z j) (x, i) -
      boundaryTerm G (fun z j => composeField G G' a φ' Ψ' z j) (x, i) =
    (liftOp N (dirichletOperator G' a ν β') *ᵥ φ') (h.incl x, i) -
      qStar G' a Ψ' (h.incl x, i) - boundaryTerm G' Ψ' (h.incl x, i) := by
  classical
  rw [liftOp_mulVec, liftOp_mulVec, dirichlet_apply, dirichlet_apply]
  have hxΩ : (x : Torus d (N₀ * L ^ k)) ∈ G.Ω 1 := x.2
  have hlapG := negLap_sub_boundary G (fun z j => composeField G G' a φ' Ψ' z j)
    (fun q => φ' (h.incl q.1, q.2)) i x
  have hlapG' := negLap_sub_boundary G' Ψ' φ' i (h.incl x)
  have hbar : ∑ μ : Fin d, (2 * φ' (h.incl x, i) -
      barField G (fun z j => composeField G G' a φ' Ψ' z j) (fun q => φ' (h.incl q.1, q.2))
        ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
      barField G (fun z j => composeField G G' a φ' Ψ' z j) (fun q => φ' (h.incl q.1, q.2))
        ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i) =
      ∑ μ : Fin d, (2 * φ' (h.incl x, i) -
      barField G' Ψ' φ' ((h.incl x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
      barField G' Ψ' φ' ((h.incl x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i) := by
    refine Finset.sum_congr rfl fun μ _ => ?_
    have e1 := barField_compose h a φ' Ψ' (y := (x : Torus d (N₀ * L ^ k)) + Pi.single μ 1)
      ((mem_dataSites G).2 (by
        by_cases hy : (x : Torus d (N₀ * L ^ k)) + Pi.single μ 1 ∈ G.Ω 1
        · exact Or.inl hy
        · exact Or.inr (mem_collar_of_adj G hxΩ hy (adj_add_single _ μ)))) i
    have e2 := barField_compose h a φ' Ψ' (y := (x : Torus d (N₀ * L ^ k)) - Pi.single μ 1)
      ((mem_dataSites G).2 (by
        by_cases hy : (x : Torus d (N₀ * L ^ k)) - Pi.single μ 1 ∈ G.Ω 1
        · exact Or.inl hy
        · exact Or.inr (mem_collar_of_adj G hxΩ hy (adj_sub_single _ μ)))) i
    rw [e1, e2]
    rfl
  -- block terms
  obtain ⟨hn1, hnk, hxn⟩ := G.layerIndex_spec hxΩ
  have hblkG : blockTerm G a (zeroExt (G.Ω 1) (fun q => φ' (h.incl q, i)))
      (x : Torus d (N₀ * L ^ k)) =
      ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
        blockMean G (G.layerIndex (x : Torus d (N₀ * L ^ k))) (fun y => svec G' φ' y i) x := by
    rw [blockTerm_zeroExt_eq]
    congr 1
    unfold blockMean
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨hy1, -⟩ := h.block_compat hxΩ hy
    rw [zeroExt_mem _ _ ⟨y, hy1⟩]
    exact (svec_of_mem G' φ' (h.incl ⟨y, hy1⟩) i).symm
  have hblkG' : blockTerm G' a (zeroExt (G'.Ω 1) (fun q => φ' (q, i)))
      (h.incl x : Torus d (N₀ * L ^ k)) =
      ((a (G'.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G'.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
        blockMean G' (G'.layerIndex (x : Torus d (N₀ * L ^ k))) (fun y => svec G' φ' y i) x :=
    rfl
  -- the algebra
  have hcomp := composeField_of_mem a φ' Ψ' hxΩ i
  have hxz : zeroExt (G.Ω 1) (fun q => φ' (h.incl q, i)) (x : Torus d (N₀ * L ^ k)) =
      φ' (h.incl x, i) := zeroExt_mem _ _ x
  have hxz' : zeroExt (G'.Ω 1) (fun q => φ' (q, i)) (h.incl x : Torus d (N₀ * L ^ k)) =
      φ' (h.incl x, i) := zeroExt_mem _ _ (h.incl x)
  have hκ : ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
      ((a (G'.layerIndex (x : Torus d (N₀ * L ^ k))) / a (G.layerIndex (x : Torus d (N₀ * L ^ k))) *
        (((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 /
          ((L : ℝ) ^ G'.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) : ℝ) : ℂ) =
      ((a (G'.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G'.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) := by
    have han := ha _ hn1 hnk
    have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  have hq : qStar G a (fun z j => composeField G G' a φ' Ψ' z j) (x, i) =
      ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
        composeField G G' a φ' Ψ' x i := rfl
  have hq' : qStar G' a Ψ' (h.incl x, i) =
      ((a (G'.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G'.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) * Ψ' x i := rfl
  rw [hblkG, hblkG', hq, hq', hcomp]
  simp only at *
  linear_combination hlapG - hlapG' + hbar + (blockMean G' (G'.layerIndex (x : Torus d (N₀ * L ^ k))) (fun y => svec G' φ' y i) x - Ψ' x i) * hκ

end Transfer

/-! ### Theorem 6.1 (ii), (iv): the composition identities -/

section Identities

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- The restriction of a field on `Ω'₁` to `Ω₁`. -/
def Precedes.restrictφ (h : Precedes G G') (φ' : G'.Ω 1 × Fin N → ℂ) : G.Ω 1 × Fin N → ℂ :=
  fun q => φ' (h.incl q.1, q.2)

/-- The restriction of a multiplier on `Ω'₁` to `Ω₁`. -/
def Precedes.restrictα (h : Precedes G G') (α' : G'.Ω 1 → ℂ) : G.Ω 1 → ℂ :=
  fun z => α' (h.incl z)

/-- The residual `H_D(α) φ - S` of the linear equation of (EL) (no constraint involved). -/
noncomputable def elResidual (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) : G.Ω 1 × Fin N → ℂ :=
  liftOp N (dirichletOperator G a ν α) *ᵥ φ - source G a ν D

/-- **Theorem 6.1 (ii), (iv): the composition identity as an identity of residuals.**  For *any*
`φ'`, `α'` (no equation and no constraint is assumed), the residual of the linear equation of
(EL) for `𝔹_j` at the composed datum, at `φ'|_{Ω₁}`, `α'|_{Ω₁}`, is the residual for `𝔹'_k` at the
sites of `Ω₁`.  Pointwise algebra, valid for complex data and any weights `a_n ≠ 0`, any mass. -/
theorem elResidual_compose (h : Precedes G G') (a : ℕ → ℝ) (ha : ∀ j, 1 ≤ j → j ≤ k → a j ≠ 0)
    (ν : ℝ) (D' : BgData G' N) (φ' : G'.Ω 1 × Fin N → ℂ) (α' : G'.Ω 1 → ℂ) (x : G.Ω 1)
    (i : Fin N) :
    elResidual G a ν (composeData h a φ' D') (h.restrictφ φ') (h.restrictα α') (x, i) =
      elResidual G' a ν D' φ' α' (h.incl x, i) := by
  have e := resid_compose h a ha ν α' φ' D'.Ψ x i
  have hh : (composeData h a φ' D').h x i = D'.h x i := by
    simp [composeData, x.2]
  unfold elResidual source
  simp only [Pi.sub_apply]
  rw [hh]
  change _ - (qStar G a (fun z j => composeField G G' a φ' D'.Ψ z j) (x, i) + _ +
    boundaryTerm G (fun z j => composeField G G' a φ' D'.Ψ z j) (x, i)) = _
  simp only [qStar] at e ⊢
  unfold Precedes.restrictφ Precedes.restrictα
  simp only [Precedes.incl_val] at e ⊢
  linear_combination e

/-- **Theorem 6.1 (ii), (iv)**: if `(φ', α')` solves (EL) for `𝔹'_k` with datum `D'` then its
restriction solves (EL) for `𝔹_j` with the composed datum.  Real or complex data. -/
theorem isEL_compose (h : Precedes G G') (a : ℕ → ℝ) (ha : ∀ j, 1 ≤ j → j ≤ k → a j ≠ 0)
    (ν : ℝ) (D' : BgData G' N) {φ' : G'.Ω 1 × Fin N → ℂ} {α' : G'.Ω 1 → ℂ}
    (hEL : IsEL G' a ν D' φ' α') :
    IsEL G a ν (composeData h a φ' D') (h.restrictφ φ') (h.restrictα α') := by
  refine ⟨?_, fun x => hEL.2 (h.incl x)⟩
  funext ⟨x, i⟩
  have e := elResidual_compose h a ha ν D' φ' α' x i
  have e0 : elResidual G' a ν D' φ' α' = 0 := by
    unfold elResidual; rw [hEL.1]; simp
  rw [e0] at e
  simp only [Pi.zero_apply] at e
  unfold elResidual at e
  exact sub_eq_zero.1 e

/-- The size restriction is inherited: `ℓ_{𝔹_j}(x)² |α'(x)| ≤ ℓ'(x)² |α'(x)|` since `n ≤ p`. -/
theorem isSmallSolution_compose (h : Precedes G G') (a : ℕ → ℝ)
    (ha : ∀ j, 1 ≤ j → j ≤ k → a j ≠ 0) (ν : ℝ) {c₀ : ℝ} (D' : BgData G' N)
    {φ' : G'.Ω 1 × Fin N → ℂ} {α' : G'.Ω 1 → ℂ} (hS : IsSmallSolution G' a ν c₀ D' φ' α') :
    IsSmallSolution G a ν c₀ (composeData h a φ' D') (h.restrictφ φ') (h.restrictα α') := by
  refine ⟨isEL_compose h a ha ν D' hS.1, fun x => ?_⟩
  have hle := h.layerIndex_le x.2
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hsp : G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 ≤ G'.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
    unfold GeneratingSet.spacing
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL hle) 2
  calc _ ≤ G'.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α' (h.incl x)‖ :=
        mul_le_mul_of_nonneg_right hsp (norm_nonneg _)
    _ < c₀ := hS.2 (h.incl x)

/-- **Theorem 6.1 (ii), identities**: if the small solution of the `𝔹_j` problem with the
composed datum is unique (Theorem 5.2 (1)), it is the restriction of the `𝔹'_k` one. -/
theorem compose_eq_of_unique (h : Precedes G G') (a : ℕ → ℝ)
    (ha : ∀ j, 1 ≤ j → j ≤ k → a j ≠ 0) (ν : ℝ) {c₀ : ℝ} (D' : BgData G' N)
    {φ' : G'.Ω 1 × Fin N → ℂ} {α' : G'.Ω 1 → ℂ} (hS : IsSmallSolution G' a ν c₀ D' φ' α')
    (hU : ∀ φ₁ φ₂ α₁ α₂, IsSmallSolution G a ν c₀ (composeData h a φ' D') φ₁ α₁ →
      IsSmallSolution G a ν c₀ (composeData h a φ' D') φ₂ α₂ → φ₁ = φ₂ ∧ α₁ = α₂)
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (hφ : IsSmallSolution G a ν c₀ (composeData h a φ' D') φ α) :
    φ = h.restrictφ φ' ∧ α = h.restrictα α' :=
  hU _ _ _ _ hφ (isSmallSolution_compose h a ha ν D' hS)

end Identities

end Balaban.Background
