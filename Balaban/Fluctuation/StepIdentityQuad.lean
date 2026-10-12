/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepObjects
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The quadratic part of the exact expansion is `½ β ⟨ψ', 𝒜 ψ'⟩` (FLUCTUATION.md §2.3, §2.4)

The covariance of Lemma 2.4 is stated through the decoupled objects (`covOp`, built from the
generating set `𝔹'` of level `k + 1`, `xH0`, the normalised block average `unitQ`), the quadratic
part of the expansion (2.4) through the Background objects (`deltaForm`, built from the generating
set `𝔹` of level `k`, `opHk`).  This file proves their identification:
for a real field `y` of the unit lattice `T^{(k)}_1`, lifted to the fine torus,
`couplingC (0, y) + ½ deltaForm(y) = ½ L^{k(d-2)} ⟨y, 𝒜 y⟩`.

* `constrainedOp_comp` and companions: relabelling of the index set commutes with
  `liftOp`, `constraintForm`, `constrainedOp`;
* `opHk_eq_xH0`: `H_k` of Lemma 2.3 is the Dirichlet operator `H₀` of the decoupled objects.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.Localization Matrix Finset

section Reindex

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {N : ℕ}

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem liftOp_submatrix (e : ι ≃ κ) (A : Matrix κ κ ℂ) :
    liftOp N (A.submatrix e e) =
      (liftOp N A).submatrix (e.prodCongr (Equiv.refl (Fin N)))
        (e.prodCongr (Equiv.refl (Fin N))) := by
  ext p q
  simp [liftOp]

omit [Fintype ι] [Fintype κ] in
theorem fieldMul_comp (e : ι ≃ κ) (φ : κ → Fin N → ℂ) :
    fieldMul (fun x => φ (e x)) =
      (fieldMul φ).submatrix (e.prodCongr (Equiv.refl (Fin N))) e := by
  ext p y
  simp [fieldMul, e.injective.eq_iff]

theorem constraintForm_comp (e : ι ≃ κ) (A : Matrix κ κ ℂ) (φ : κ → Fin N → ℂ) :
    constraintForm (A.submatrix e e) (fun x => φ (e x)) = (constraintForm A φ).submatrix e e := by
  unfold constraintForm
  rw [liftOp_submatrix, fieldMul_comp, Matrix.transpose_submatrix]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

theorem constrainedOp_comp (e : ι ≃ κ) (A : Matrix κ κ ℂ) (φ : κ → Fin N → ℂ) :
    constrainedOp (A.submatrix e e) (fun x => φ (e x)) =
      (constrainedOp A φ).submatrix (e.prodCongr (Equiv.refl (Fin N)))
        (e.prodCongr (Equiv.refl (Fin N))) := by
  unfold constrainedOp
  rw [liftOp_submatrix, fieldMul_comp, constraintForm_comp, Matrix.inv_submatrix_equiv,
    Matrix.transpose_submatrix]
  simp only [Matrix.submatrix_mul_equiv]

end Reindex

section Operator

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- For a generating set of level `n`, the layers other than `n` are empty. -/
theorem IsLevel.not_mem_layer {K n : ℕ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    (hG : IsLevel G n) {j : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ K) (hne : j ≠ n)
    (x : Torus d (N₁ * L ^ m₁ * L ^ K)) : x ∉ G.layer j :=
  fun hx => G.layer_disjoint (hG.bounds.1) (hG.bounds.2) hj1 hjK (Ne.symm hne) (hG.mem_layer x) hx

/-- The relabelling `Ω₁ ≃ Ω'₁` for the levels `k` and `k + 1` (both are the whole torus). -/
noncomputable def levelEquiv (hG : IsLevel G k) (hG' : IsLevel G' (k + 1)) : G.Ω 1 ≃ G'.Ω 1 :=
  Equiv.ofBijective (hG.precedes hG' (le_refl (k + 1))).incl
    ⟨fun x y h => Subtype.ext
        (congrArg (fun z : G'.Ω 1 => (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1)))) h),
      fun y => ⟨⟨y.1, by rw [hG.Ω_one]; exact Finset.mem_univ _⟩, Subtype.ext rfl⟩⟩

theorem levelEquiv_val (hG : IsLevel G k) (hG' : IsLevel G' (k + 1)) (x : G.Ω 1) :
    ((levelEquiv hG hG' x : G'.Ω 1) : Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) = x := rfl

/-- The real matrix `-Δ + ν + Q* a Q` of the level-`k` set is `-Δ + ν` plus the block projection of
side `L^k` on the layer `k + 1` of the level-`(k+1)` set. -/
theorem fullMatrix_eq (hG : IsLevel G k) (hG' : IsLevel G' (k + 1)) (a : ℕ → ℝ) (ν : ℝ) :
    fullMatrix G a ν =
      latticeLaplacian d (N₁ * L ^ m₁ * L ^ (k + 1)) ν + xAvg0 G' a +
        (a k / ((L : ℝ) ^ k) ^ 2) • layerBlockMatrix G' (k + 1) k := by
  have hk := hG.bounds
  unfold fullMatrix avgMatrix xAvg0
  rw [add_assoc]
  congr 1
  rw [Finset.sum_eq_single k]
  · have : layerProjMatrix G k = layerBlockMatrix G' (k + 1) k := by
      ext x x'
      simp only [layerProjMatrix, layerBlockMatrix, hG.mem_layer x, hG.mem_layer x',
        hG'.mem_layer x, hG'.mem_layer x', and_self, ite_true]
    rw [this]
    have h0 : ∑ j ∈ Finset.Icc 1 k, (a j / ((L : ℝ) ^ j) ^ 2) • layerBlockMatrix G' j j = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' := Finset.mem_Icc.1 hj
      have : layerBlockMatrix G' j j = 0 := by
        ext x x'
        have hn : ¬ (x ∈ G'.layer j ∧ x' ∈ G'.layer j) :=
          fun h => hG'.not_mem_layer hj'.1 (by omega) (by omega) x h.1
        simp [layerBlockMatrix, hn]
      rw [this, smul_zero]
    rw [h0, zero_add]
  · intro j hj hjk
    have hj' := Finset.mem_Icc.1 hj
    have : layerProjMatrix G j = 0 := by
      ext x x'
      have hn : ¬ (x ∈ G.layer j ∧ x' ∈ G.layer j) :=
        fun h => hG.not_mem_layer hj'.1 hj'.2 hjk x h.1
      simp [layerProjMatrix, hn]
    rw [this, smul_zero]
  · intro hk'
    exact absurd (Finset.mem_Icc.2 ⟨hk.1, by omega⟩) hk'

/-- **`H_k` of Lemma 2.3 is the Dirichlet operator `H₀` of the decoupled objects** (Lemma 2.4). -/
theorem opHk_eq_xH0 (hG : IsLevel G k) (hG' : IsLevel G' (k + 1)) (a : ℕ → ℝ) (ν : ℝ)
    (α₁ : G'.Ω 1 → ℂ) :
    Balaban.Fluctuation.opHk (hG.precedes hG' (le_refl (k + 1))) a ν α₁ =
      (xH0 G' a ν α₁).submatrix (levelEquiv hG hG') (levelEquiv hG hG') := by
  ext x y
  have hfm := fullMatrix_eq hG hG' a ν
  simp only [Balaban.Fluctuation.opHk, dirichletOperator, xH0, xHt, Pk, Green.restrictOp,
    Matrix.add_apply, Matrix.smul_apply, Matrix.submatrix_apply, Matrix.diagonal_apply, hfm,
    Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, map_mul, smul_eq_mul,
    Precedes.restrictα, levelEquiv_val]
  have hxy : (levelEquiv hG hG' x = levelEquiv hG hG' y) ↔ x = y :=
    (levelEquiv hG hG').injective.eq_iff
  have e : (levelEquiv hG hG') x = (hG.precedes hG' (le_refl (k + 1))).incl x := rfl
  simp only [hxy, Complex.coe_algebraMap]
  split_ifs with h
  · subst h; rw [e]; ring
  · ring

end Operator

section Counting

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **Summation over the fine torus of a function of the unit block**: each unit block contains
`L^{kd}` fine sites. -/
theorem sum_fine_unit (hG' : IsLevel G' (k + 1)) (F : UnitTorus d L N₁ m₁ k → ℂ) :
    ∑ x : CTorus d L N₁ m₁ (k + 1), F (unitBlock x) =
      (((L : ℝ) ^ k) ^ d : ℝ) * ∑ b : unitPts G', F b := by
  classical
  have hmaps : ∀ x ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))),
      unitBlock x ∈ unitPts G' := fun x _ => (unitBlock_mem_iff G' x).2 (hG'.mem_layer x)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [Finset.mul_sum, ← Finset.sum_coe_sort (unitPts G')]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hc : ((Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))).filter
      fun x => unitBlock x = (b : UnitTorus d L N₁ m₁ k)).card = (L ^ k) ^ d := by
    have := card_unit_fibre G' b.2
    rwa [hG'.Ω_one] at this
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2] :
    ∀ x ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))).filter
      (fun x => unitBlock x = (b : UnitTorus d L N₁ m₁ k)), F (unitBlock x) = F b),
    Finset.sum_const, hc]
  simp [nsmul_eq_mul]

end Counting

section BlockMean

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **The block mean over `(k+1)`-blocks of a lift of a unit-lattice function is `P`**:
`(Q_{k+1} g(unitBlock ·))(x) = (P g)(unitBlock x)`. -/
theorem blockMean_unit (hG' : IsLevel G' (k + 1)) (g : UnitTorus d L N₁ m₁ k → ℂ)
    (x : CTorus d L N₁ m₁ (k + 1)) :
    blockMean G' (k + 1) (fun y => g (unitBlock y)) x =
      ∑ b' : unitPts G', unitP G' (unitPt hG' x) b' * g b' := by
  classical
  unfold blockMean
  have hsum : ∑ y ∈ G'.blk (k + 1) x, g (unitBlock y) =
      ∑ y : CTorus d L N₁ m₁ (k + 1),
        (fun b : UnitTorus d L N₁ m₁ k =>
          if unitBlock1 b = unitBlock1 (unitBlock x) then g b else 0) (unitBlock y) := by
    unfold GeneratingSet.blk
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [unitBlock1_unitBlock]
  have h2 := sum_fine_unit hG' (fun b : UnitTorus d L N₁ m₁ k =>
          if unitBlock1 b = unitBlock1 (unitBlock x) then g b else 0)
  calc ((((((L : ℝ) ^ (k + 1)) ^ d)⁻¹ : ℝ) : ℂ)) * ∑ y ∈ G'.blk (k + 1) x, g (unitBlock y)
      = ((((((L : ℝ) ^ (k + 1)) ^ d)⁻¹ : ℝ) : ℂ)) * (((((L : ℝ) ^ k) ^ d : ℝ) : ℂ) *
          ∑ b : unitPts G', (if unitBlock1 (b : UnitTorus d L N₁ m₁ k) =
            unitBlock1 (unitBlock x) then g b else 0)) := by rw [hsum, h2]
    _ = ∑ b' : unitPts G', unitP G' (unitPt hG' x) b' * g b' := by
      rw [← mul_assoc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      simp only [unitP, unitPt]
      by_cases h : unitBlock1 (b' : UnitTorus d L N₁ m₁ k) = unitBlock1 (unitBlock x)
      · have h' : unitBlock1 (unitBlock x) = unitBlock1 (b' : UnitTorus d L N₁ m₁ k) := h.symm
        have hc := eq_true h
        have hc' := eq_true h'
        simp only [hc, hc', ↓reduceIte]
        have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
        congr 1
        rw [← Complex.ofReal_mul]
        congr 1
        push_cast
        rw [pow_succ]
        field_simp
        ring
      · have h' : ¬ unitBlock1 (unitBlock x) = unitBlock1 (b' : UnitTorus d L N₁ m₁ k) :=
          fun e => h e.symm
        have hc := eq_false h
        have hc' := eq_false h'
        simp only [hc, hc', ↓reduceIte, mul_zero, zero_mul]

end BlockMean

section Coupling

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- The complexification of a real field of the unit lattice, as a vector on `T^{(k)}_1 × [N]`. -/
def yhat (y : unitPts G' → Rn N) : unitPts G' × Fin N → ℂ := fun q => ((y q.1 q.2 : ℝ) : ℂ)

theorem unitP_transpose : (unitP G')ᵀ = unitP G' := by
  ext b b'
  simp only [Matrix.transpose_apply, unitP]
  simp only [eq_comm]

theorem unitP_dot (v : unitPts G' → ℂ) :
    (unitP G' *ᵥ v) ⬝ᵥ (unitP G' *ᵥ v) = v ⬝ᵥ (unitP G' *ᵥ v) := by
  have hP : (unitP G') * (unitP G') = unitP G' := unitP_idem G'
  calc (unitP G' *ᵥ v) ⬝ᵥ (unitP G' *ᵥ v)
      = ((unitP G')ᵀ *ᵥ (unitP G' *ᵥ v)) ⬝ᵥ v := by
        rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    _ = (unitP G' *ᵥ v) ⬝ᵥ v := by
        rw [unitP_transpose, Matrix.mulVec_mulVec, hP]
    _ = v ⬝ᵥ (unitP G' *ᵥ v) := dotProduct_comm _ _

/-- **The coupling term on a lifted unit-lattice field** (the `P`-part of `𝒜`):
`½ a₁ L^{-2(k+1)} ∑_x |Q_{k+1} y|² = ½ (a₁/L²) L^{k(d-2)} ⟨y, P y⟩`. -/
theorem couplingC_unit (hG' : IsLevel G' (k + 1)) (a₁ : ℝ) (y : unitPts G' → Rn N) :
    couplingC G' a₁ (k + 1) (fun _ _ => 0)
        (fun x i => ((liftU hG' y x i : ℝ) : ℂ)) =
      ((((1 / 2) * (a₁ / (L : ℝ) ^ 2) * (((L : ℝ) ^ k) ^ d / ((L : ℝ) ^ k) ^ 2) : ℝ)) : ℂ) *
        (yhat y ⬝ᵥ (liftOp N (unitP G') *ᵥ yhat y)) := by
  classical
  unfold couplingC
  -- the function of the unit block
  set g : Fin N → UnitTorus d L N₁ m₁ k → ℂ := fun i b =>
    if h : b ∈ unitPts G' then ((y ⟨b, h⟩ i : ℝ) : ℂ) else 0 with hg
  have hlift : ∀ i x, ((liftU hG' y x i : ℝ) : ℂ) = g i (unitBlock x) := by
    intro i x
    have hb := (unitBlock_mem_iff G' x).2 (hG'.mem_layer x)
    simp [hg, liftU, unitPt, hb]
  have hM : ∀ i x, blockMean G' (k + 1) (fun z => ((liftU hG' y z i : ℝ) : ℂ)) x =
      (unitP G' *ᵥ fun b => yhat y (b, i)) (unitPt hG' x) := by
    intro i x
    have := blockMean_unit hG' (g i) x
    simp only [hlift]
    rw [this]
    simp only [Matrix.mulVec, dotProduct, yhat, hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [b.2]
  simp only [hM]
  have hF : ∀ i, ∑ x : CTorus d L N₁ m₁ (k + 1),
      (0 - (unitP G' *ᵥ fun b => yhat y (b, i)) (unitPt hG' x)) *
        (0 - (unitP G' *ᵥ fun b => yhat y (b, i)) (unitPt hG' x)) =
      ((((L : ℝ) ^ k) ^ d : ℝ) : ℂ) *
        ((unitP G' *ᵥ fun b => yhat y (b, i)) ⬝ᵥ (unitP G' *ᵥ fun b => yhat y (b, i))) := by
    intro i
    set w : unitPts G' → ℂ := unitP G' *ᵥ fun b => yhat y (b, i) with hw
    have h1 := sum_fine_unit hG' (fun b => if h : b ∈ unitPts G' then w ⟨b, h⟩ * w ⟨b, h⟩ else 0)
    have h2 : ∀ x : CTorus d L N₁ m₁ (k + 1),
        (0 - w (unitPt hG' x)) * (0 - w (unitPt hG' x)) =
          (fun b => if h : b ∈ unitPts G' then w ⟨b, h⟩ * w ⟨b, h⟩ else 0) (unitBlock x) := by
      intro x
      have hb := (unitBlock_mem_iff G' x).2 (hG'.mem_layer x)
      simp [unitPt, hb]
    simp only [h2]
    rw [h1]
    congr 1
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [b.2]
  rw [Finset.sum_comm]
  simp only [hF]
  simp only [unitP_dot, ← Finset.mul_sum]
  have hR : yhat y ⬝ᵥ (liftOp N (unitP G') *ᵥ yhat y) =
      ∑ i : Fin N, (fun b => yhat y (b, i)) ⬝ᵥ (unitP G' *ᵥ fun b => yhat y (b, i)) := by
    simp only [dotProduct, Fintype.sum_prod_type, liftOp_mulVec]
    rw [Finset.sum_comm]
  rw [hR]
  have hLk : (((L : ℝ) ^ (k + 1)) ^ 2) = ((L : ℝ) ^ 2) * ((L : ℝ) ^ k) ^ 2 := by ring
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLk0 : (0 : ℝ) < ((L : ℝ) ^ k) := by positivity
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  rw [hLk]
  field_simp

end Coupling

section Delta

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- `fieldBase` is `φ_{k+1}` restricted to the torus, composed with the relabelling. -/
theorem fieldBase_eq_comp (hG : IsLevel G k) (hG' : IsLevel G' (k + 1))
    (φ₁ : G'.Ω 1 × Fin N → ℂ) :
    Balaban.Fluctuation.fieldBase (hG.precedes hG' (le_refl (k + 1))) φ₁ =
      fun x => restrictField G' (svec G' φ₁) (levelEquiv hG hG' x) := by
  funext x i
  simp only [Balaban.Fluctuation.fieldBase, Precedes.restrictφ, restrictField]
  rw [svec_eq_apply hG' φ₁]
  rfl

/-- **`⟨S, φ^{(1)}[S]⟩` through the decoupled operators**: the pairing of the linear response of
Lemma 2.3 with its data, in the decoupled notation of Lemma 2.4. -/
theorem pair_phiOne (hG : IsLevel G k) (hG' : IsLevel G' (k + 1)) (a : ℕ → ℝ) (ν : ℝ)
    (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ) (S : G.Ω 1 × Fin N → ℂ) :
    pair G S (Balaban.Fluctuation.phiOne (hG.precedes hG' (le_refl (k + 1))) a ν α₁ φ₁ S) =
      (S ∘ (levelEquiv hG hG').symm.prodCongr (Equiv.refl (Fin N))) ⬝ᵥ
        ((liftOp N (xH0 G' a ν α₁)⁻¹ -
            constrainedOp (xH0 G' a ν α₁)⁻¹ (restrictField G' (svec G' φ₁))) *ᵥ
          (S ∘ (levelEquiv hG hG').symm.prodCongr (Equiv.refl (Fin N)))) := by
  classical
  set e := levelEquiv hG hG' with he
  set E := e.prodCongr (Equiv.refl (Fin N)) with hE
  have hop := opHk_eq_xH0 hG hG' a ν α₁
  have hfb := fieldBase_eq_comp hG hG' φ₁
  unfold Balaban.Fluctuation.phiOne
  rw [hop, hfb, Matrix.inv_submatrix_equiv, constrainedOp_comp, liftOp_submatrix]
  have hsub : ∀ (A B : Matrix (G'.Ω 1 × Fin N) (G'.Ω 1 × Fin N) ℂ),
      A.submatrix E E - B.submatrix E E = (A - B).submatrix E E := fun A B => rfl
  rw [hsub, Matrix.submatrix_mulVec_equiv]
  unfold pair
  rw [dotProduct]
  rw [← Equiv.sum_comp E]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hE' : ⇑E.symm = ⇑(e.symm.prodCongr (Equiv.refl (Fin N))) := rfl
  have hp : (e.symm.prodCongr (Equiv.refl (Fin N))) (E p) = p := by
    rw [← hE']; exact E.symm_apply_apply p
  rw [hE']
  simp only [Function.comp_apply, hp]

end Delta

section Delta2

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- `Q* ŷ`: the fine-torus vector `x ↦ Q(unitBlock x, x) ŷ(unitBlock x)`. -/
noncomputable def Qt (y : unitPts G' → Rn N) : G'.Ω 1 × Fin N → ℂ :=
  (liftRect N (unitQ G'))ᵀ *ᵥ yhat y

/-- The entry of `Q`: `τ = (L^{kd})^{-1/2}`. -/
noncomputable def tauQ (d L k : ℕ) : ℝ := Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹)

theorem Qt_apply (hG' : IsLevel G' (k + 1)) (y : unitPts G' → Rn N) (x : G'.Ω 1) (i : Fin N) :
    Qt y (x, i) = (tauQ d L k : ℂ) * yhat y (unitPt hG' x.1, i) := by
  classical
  unfold Qt
  rw [liftRect_transpose, liftRect_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [Finset.sum_eq_single (unitPt hG' x.1)]
  · simp [unitQ, unitPt, tauQ]
  · intro b _ hb
    have : unitBlock (x.1 : CTorus d L N₁ m₁ (k + 1)) ≠ (b : UnitTorus d L N₁ m₁ k) := by
      intro e; exact hb (Subtype.ext e.symm)
    simp [unitQ, this]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [NeZero L] in
theorem tauQ_sq : (tauQ d L k) ^ 2 = ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹) := by
  unfold tauQ
  rw [Real.sq_sqrt]
  positivity

end Delta2

section Delta3

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **`deltaForm` on a lifted unit-lattice field**, in the decoupled notation of Lemma 2.4:
`a_k L^{-2k} ‖y‖² L^{kd} - (a_k L^{-2k})² L^{kd} ⟨Q*y, (G_D - Π_D) Q*y⟩`. -/
theorem deltaForm_unit (hG : IsLevel G k) (hG' : IsLevel G' (k + 1)) (a : ℕ → ℝ) (ν : ℝ)
    (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ) (y : unitPts G' → Rn N) :
    Balaban.Fluctuation.deltaForm (hG.precedes hG' (le_refl (k + 1))) a ν α₁ φ₁
        (fun x i => ((liftU hG' y x i : ℝ) : ℂ)) =
      ((((L : ℝ) ^ k) ^ d : ℝ) : ℂ) * (((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) *
          (yhat y ⬝ᵥ yhat y) -
        ((a k / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) ^ 2 *
          (Qt y ⬝ᵥ ((liftOp N (xH0 G' a ν α₁)⁻¹ -
            constrainedOp (xH0 G' a ν α₁)⁻¹ (restrictField G' (svec G' φ₁))) *ᵥ Qt y))) := by
  classical
  set ψ'c : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ := fun x i => ((liftU hG' y x i : ℝ) : ℂ) with hψ
  set cK : ℝ := a k / ((L : ℝ) ^ k) ^ 2 with hcK
  have hS : ∀ p : G.Ω 1 × Fin N, qStar G a ψ'c p = (cK : ℂ) * ψ'c p.1 p.2 := by
    intro p
    simp only [qStar, hψ]
    rw [(hG p.1.1).2]
  unfold Balaban.Fluctuation.deltaForm
  rw [pair_phiOne hG hG']
  -- first pair
  have h1 : pair G (fun p => ψ'c p.1 p.2) (qStar G a ψ'c) =
      ((((L : ℝ) ^ k) ^ d : ℝ) : ℂ) * ((cK : ℂ) * (yhat y ⬝ᵥ yhat y)) := by
    unfold pair
    simp only [hS, Fintype.sum_prod_type]
    rw [hG.sum_ΩC (fun x => ∑ i, ψ'c x i * ((cK : ℂ) * ψ'c x i))]
    rw [Finset.sum_comm]
    have hgi : ∀ i, ∑ x : CTorus d L N₁ m₁ (k + 1), ψ'c x i * ((cK : ℂ) * ψ'c x i) =
        ((((L : ℝ) ^ k) ^ d : ℝ) : ℂ) * ((cK : ℂ) * ∑ b : unitPts G', yhat y (b, i) * yhat y (b, i)) := by
      intro i
      have h1 := sum_fine_unit hG' (fun b => if h : b ∈ unitPts G' then
        (cK : ℂ) * (yhat y (⟨b, h⟩, i) * yhat y (⟨b, h⟩, i)) else 0)
      have h2 : ∀ x : CTorus d L N₁ m₁ (k + 1), ψ'c x i * ((cK : ℂ) * ψ'c x i) =
          (fun b => if h : b ∈ unitPts G' then
            (cK : ℂ) * (yhat y (⟨b, h⟩, i) * yhat y (⟨b, h⟩, i)) else 0) (unitBlock x) := by
        intro x
        have hb := (unitBlock_mem_iff G' x).2 (hG'.mem_layer x)
        simp [hψ, liftU, unitPt, yhat, hb]
        ring
      simp only [h2]
      rw [h1]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [b.2]
    simp only [hgi]
    simp only [dotProduct, Fintype.sum_prod_type]
    rw [Finset.sum_comm (f := fun b i => yhat y (b, i) * yhat y (b, i))]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hτ : 0 < tauQ d L k := by
    unfold tauQ
    refine Real.sqrt_pos.2 ?_
    have : (0 : ℝ) < ((L ^ k : ℕ) : ℝ) := by exact_mod_cast pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k
    positivity
  have hτC : (tauQ d L k : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hQ : (qStar G a ψ'c) ∘ ⇑((levelEquiv hG hG').symm.prodCongr (Equiv.refl (Fin N))) =
      ((cK : ℂ) * (tauQ d L k : ℂ)⁻¹) • Qt y := by
    funext q
    obtain ⟨x, i⟩ := q
    have hx : (((levelEquiv hG hG').symm x : G.Ω 1) : CTorus d L N₁ m₁ (k + 1)) = x.1 := by
      have := levelEquiv_val hG hG' ((levelEquiv hG hG').symm x)
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Equiv.prodCongr_apply, Prod.map_apply,
      Equiv.refl_apply]
    rw [hS, Qt_apply hG']
    simp only [hψ, liftU, yhat, hx]
    field_simp
  rw [hQ]
  have hτ2 : ((tauQ d L k : ℂ)⁻¹) ^ 2 = ((((L : ℝ) ^ k) ^ d : ℝ) : ℂ) := by
    have h := tauQ_sq (d := d) (L := L) (k := k)
    have h' : ((tauQ d L k : ℂ)) ^ 2 = (((((L ^ k : ℕ) : ℝ) ^ d)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h
    rw [inv_pow, h']
    push_cast
    simp
  rw [h1]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  have : (((cK : ℂ) * (tauQ d L k : ℂ)⁻¹) * (((cK : ℂ) * (tauQ d L k : ℂ)⁻¹) *
      (Qt y ⬝ᵥ ((liftOp N (xH0 G' a ν α₁)⁻¹ -
            constrainedOp (xH0 G' a ν α₁)⁻¹ (restrictField G' (svec G' φ₁))) *ᵥ Qt y)))) =
      ((((L : ℝ) ^ k) ^ d : ℝ) : ℂ) * ((cK : ℂ) ^ 2 *
      (Qt y ⬝ᵥ ((liftOp N (xH0 G' a ν α₁)⁻¹ -
            constrainedOp (xH0 G' a ν α₁)⁻¹ (restrictField G' (svec G' φ₁))) *ᵥ Qt y))) := by
    rw [← hτ2]; ring
  rw [this]
  ring

end Delta3

section QuadFinal

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **`ŷ ⬝ 𝒜 ŷ`** in terms of the pieces: the quadratic form of `covOp`. -/
theorem covOp_quad (a : ℕ → ℝ) (aT ν : ℝ) (α : G'.Ω 1 → ℂ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (y : unitPts G' → Rn N) :
    yhat y ⬝ᵥ (covOp G' a aT ν α φ (unitQ G') (unitP G') *ᵥ yhat y) =
      ((a k : ℝ) : ℂ) * (yhat y ⬝ᵥ yhat y) +
        ((aT / (L : ℝ) ^ 2 : ℝ) : ℂ) * (yhat y ⬝ᵥ (liftOp N (unitP G') *ᵥ yhat y)) -
        (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) *
          (Qt y ⬝ᵥ ((liftOp N (xH0 G' a ν α)⁻¹ -
            constrainedOp (xH0 G' a ν α)⁻¹ (restrictField G' φ)) *ᵥ Qt y)) := by
  classical
  unfold covOp
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
  congr 2
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose]
  simp only [Qt, Matrix.sub_mulVec, dotProduct_sub]

end QuadFinal

section QuadFinal2

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **The quadratic part of the exact expansion is `½ L^{k(d-2)} ⟨y, 𝒜 y⟩`** (Lemma 2.3 (b) with
Lemma 2.4): for a real field `y` of the unit lattice, lifted to the fine torus,
`couplingC (0, y) + ½ deltaForm(y) = ½ L^{k(d-2)} ⟨y, 𝒜 y⟩`, `𝒜 = a L⁻² Q*Q + Δ^{(k)} = covOp`. -/
theorem quad_identity (hG : IsLevel G k) (hG' : IsLevel G' (k + 1)) (a : ℕ → ℝ) (a₁ ν : ℝ)
    (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ) (y : unitPts G' → Rn N) :
    couplingC G' a₁ (k + 1) (fun _ _ => 0) (fun x i => ((liftU hG' y x i : ℝ) : ℂ)) +
        (1 / 2 : ℂ) * Balaban.Fluctuation.deltaForm (hG.precedes hG' (le_refl (k + 1))) a ν α₁ φ₁
          (fun x i => ((liftU hG' y x i : ℝ) : ℂ)) =
      (((1 / 2) * (((L : ℝ) ^ k) ^ d / ((L : ℝ) ^ k) ^ 2) : ℝ) : ℂ) *
        (yhat y ⬝ᵥ (covOp G' a a₁ ν α₁ (svec G' φ₁) (unitQ G') (unitP G') *ᵥ yhat y)) := by
  rw [couplingC_unit hG' a₁ y, deltaForm_unit hG hG' a ν α₁ φ₁ y, covOp_quad]
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLk : (0 : ℝ) < (L : ℝ) ^ k := by positivity
  have h2k : (L : ℝ) ^ (2 * k) = ((L : ℝ) ^ k) ^ 2 := pow_mul' _ _ _
  rw [h2k]
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  push_cast
  field_simp
  ring

end QuadFinal2

end Balaban.Fluctuation
