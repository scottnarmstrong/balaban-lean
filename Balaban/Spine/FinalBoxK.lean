/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalMass
public import Balaban.Spine.FinalChain
public import Balaban.LargeField.R.ChiBridgeHist

/-!
# The quadratic form of the box integral is the Hessian of the main action

The box integral `Ξ_box` (`sfBoxIntegral`, `Spine/LastIntegral.lean`) is the Gaussian average at the
form `K = β_k D` (`sfFinalK`), `D` the final Hessian of the unit lattice read on the `k`-blocks. This
file checks that `K` is the form of P4 (6.4)–(6.6):

* `pdQuad_sfFinalK`: `Q_K(v) = β_k L^{-k(d-2)} ⟨v, H v⟩` with `H = L^{k(d-2)} D` on the `k`-blocks
  (`sfFinalHm`), so the cancellation of `sfGaussIntegrand_cubic` applies with `Kq = sfFinalK` and
  `Hm = sfFinalHm`;
* `actStar2_univ_hessian_sfFinalHm`: for a member of the class (field clauses, so the action and
  background masses are equal), `A*_k(univ; h + t u) / t² → ½ ⟨u, H u⟩`: `½ Q_K` is the quadratic part
  of `β_k L^{-k(d-2)} A*_k(h + ·)`, the action term of the exponent of the small-field factor (`Ares2`),
  and the remainder `V³ = A*_k - ½⟨v, H v⟩` of `sfGaussIntegrand_cubic` is `o(|v|²)`;
* `sfFinalK_posDef`: `K` is positive definite for `β_k > 0`, `0 < ν_k ≤ 1`, `a_k ≥ 1/2`, `|h| = 1`.
-/

@[expose] public section

open Matrix Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2 Balaban.Green

namespace Balaban.RootFSpine

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- **The Hessian of `A*_k(univ; ·)` on the `k`-blocks**: `H = L^{k(d-2)} D`, `D` the final Hessian
of the unit lattice (`finalHessian`, mass `μ_k L^{2k}`, weight `a_k`, direction `h`) read on the
`k`-blocks through `sfBlockSite`. -/
noncomputable def sfFinalHm (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N)) :
    Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ :=
  Matrix.submatrix ((((S.L : ℝ) ^ k) ^ (S.d - 2)) • finalHessian S.d
      (C.geo.M1 * (C.geo.c * n k) * S.L ^ k) (S.L ^ k)
      (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2)
      (C.weights k) (fun i => hv i))
    (fun p => (sfBlockSite C p.1, p.2)) (fun p => (sfBlockSite C p.1, p.2))

/-- `β_k L^{-k(d-2)} · L^{k(d-2)} = β_k`. -/
theorem betaCanon_mul_pow (β : ℝ) (d L k : ℕ) [NeZero L] :
    betaCanon d L β k 0 * ((L : ℝ) ^ k) ^ (d - 2) = β := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  unfold betaCanon
  rw [Nat.sub_zero, ← pow_mul, div_mul_cancel₀ _ (pow_ne_zero _ hL)]

/-- The quadratic form `Q_A` of real fields is `⟨v, A v⟩`. -/
theorem pdQuad_eq_dotProduct {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (v : ι → ℝ) :
    pdQuad A v = v ⬝ᵥ (A *ᵥ v) := by
  unfold pdQuad pdBil
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, inner, star_trivial, RCLike.re_to_real]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- **The quadratic form of the box integral**: `Q_K(v) = β_k L^{-k(d-2)} ⟨v, H v⟩`
(`K = sfFinalK`, `H = sfFinalHm`), the hypothesis of `sfGaussIntegrand_cubic`. -/
theorem pdQuad_sfFinalK (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
    (v : BlockAt S n M K k × Fin N → ℝ) :
    pdQuad (sfFinalK C hv) v = betaCanon S.d S.L (C.sf.β k) k 0 * (v ⬝ᵥ (sfFinalHm C hv *ᵥ v)) := by
  have e : sfFinalK C hv = (betaCanon S.d S.L (C.sf.β k) k 0) • sfFinalHm C hv := by
    ext p q
    simp only [sfFinalK, sfFinalHm, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← mul_assoc (betaCanon S.d S.L (C.sf.β k) k 0), betaCanon_mul_pow]
  rw [e, pdQuad_eq_dotProduct, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The block field of `blockCfgOf` at `q = i = k` is the field `u` read through `sfBlockSite`. -/
theorem blockCfgOf_sfBlockSite (C : SFCtx S n R M K N k m₁ ϱ)
    (u : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (y : BlockAt S n M K k) (i : Fin N) :
    blockCfgOf C.geo C.hnn le_rfl C.hkK u (sfBlockSite C y) i = u y i := by
  unfold blockCfgOf sfBlockSite
  rw [torusCast_cast_symm]

/-- **The form of the final Hessian at the block field is the form of `sfFinalHm`**:
`L^{k(d-2)} ⟨U, D U⟩ = ⟨v, H v⟩`, `U = blockCfgOf u`, `v = spinField u`. -/
theorem quad_blockCfgOf_eq (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
    (u : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    ((S.L : ℝ) ^ k) ^ (S.d - 2) *
      ((fun p : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) × Fin N =>
          blockCfgOf C.geo C.hnn le_rfl C.hkK u p.1 p.2) ⬝ᵥ
        (finalHessian S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ k) (S.L ^ k)
          (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k))
          (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) (fun i => hv i) *ᵥ
        (fun p : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) × Fin N =>
          blockCfgOf C.geo C.hnn le_rfl C.hkK u p.1 p.2))) =
      spinField (BlockAt S n M K k) N u ⬝ᵥ
        (sfFinalHm C hv *ᵥ spinField (BlockAt S n M K k) N u) := by
  set e : BlockAt S n M K k × Fin N ≃ Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) × Fin N :=
    ((Equiv.ofBijective (sfBlockSite C) ⟨torusCast_injective _, fun z =>
      ⟨torusCast (histScale_eq C.geo.hM C.hnn le_rfl C.hkK) z, torusCast_symm_cast _ z⟩⟩)).prodCongr
      (Equiv.refl _) with he
  have hU : (fun p : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) × Fin N =>
      blockCfgOf C.geo C.hnn le_rfl C.hkK u p.1 p.2) ∘ e = spinField (BlockAt S n M K k) N u := by
    funext p
    simp only [Function.comp_apply, he, Equiv.prodCongr_apply,
      Equiv.refl_apply, Prod.map, spinField_apply]
    exact blockCfgOf_sfBlockSite C u p.1 p.2
  have hD : sfFinalHm C hv = (((S.L : ℝ) ^ k) ^ (S.d - 2) • finalHessian S.d
      (C.geo.M1 * (C.geo.c * n k) * S.L ^ k) (S.L ^ k)
      (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2)
      (C.weights k) (fun i => hv i)).submatrix e e := rfl
  have hcomp : ∀ W : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) × Fin N → ℝ,
      ((fun p : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) × Fin N =>
          blockCfgOf C.geo C.hnn le_rfl C.hkK u p.1 p.2) ∘ e) ⬝ᵥ (W ∘ e) =
        (fun p : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) × Fin N =>
          blockCfgOf C.geo C.hnn le_rfl C.hkK u p.1 p.2) ⬝ᵥ W := fun W => by
    simp only [dotProduct, Function.comp_apply]
    exact Equiv.sum_comp e (fun z => blockCfgOf C.geo C.hnn le_rfl C.hkK u z.1 z.2 * W z)
  have hinv : ((fun p : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) × Fin N =>
      blockCfgOf C.geo C.hnn le_rfl C.hkK u p.1 p.2) ∘ e) ∘ e.symm =
      fun p : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) × Fin N =>
        blockCfgOf C.geo C.hnn le_rfl C.hkK u p.1 p.2 := by
    funext p; simp
  rw [hD, ← hU, Matrix.submatrix_mulVec_equiv, hinv, hcomp, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]

/-- **The Hessian of `A*_k(univ; ·)` at the constant configuration in the block variables**
(A6-3 (a)): for a member of the class (`FieldClauses`, so the action and background masses agree),
`A*_k(univ; h + t u) / t² → ½ ⟨v, H v⟩` with `v = spinField u` and `H = sfFinalHm`. -/
theorem actStar2_univ_hessian_sfFinalHm {k0 : ℕ} (C : SFCtx S n R M K N k m₁ ϱ)
    (hv : EuclideanSpace ℝ (Fin N)) (h : FieldClauses S k0 k C.cs C.sf hv)
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.muBg k))
    (he : ∑ i, hv i ^ 2 = 1) (hk : 1 ≤ k) (hd2 : 2 ≤ S.d)
    (u : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    Filter.Tendsto (fun t : ℝ => actStar2 C Set.univ (fun z => hv + t • u z) hv / t ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((1 / 2) * (spinField (BlockAt S n M K k) N u ⬝ᵥ
        (sfFinalHm C hv *ᵥ spinField (BlockAt S n M K k) N u)))) := by
  rw [← quad_blockCfgOf_eq C hv u]
  exact actStar2_univ_hessian_of_field C hv h H he hk hd2 u

/-- **`K = β_k D` is positive definite** for `β_k > 0`, unit-lattice mass `0 < ν_k ≤ 1`, weight
`a_k ≥ 1/2` and a unit direction `h` (symmetry `finalHessian_transpose`, coercivity
`finalHessian_form_ge_mass`). -/
theorem sfFinalK_posDef (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
    (hβ : 0 < C.sf.β k) (hν : 0 < C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2)
    (hν1 : C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2 ≤ 1) (ha : 1 / 2 ≤ C.weights k)
    (he : ∑ i, hv i ^ 2 = 1) (hd : 0 < S.d) : (sfFinalK C hv).PosDef := by
  have hℓ : C.geo.M1 * (C.geo.c * n k) * S.L ^ k =
      S.L ^ k * (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) := by
    rw [Nat.sub_self, pow_zero, mul_one, Nat.mul_comm]
  have hN : 0 < S.L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) k
  have ha0 : 0 < C.weights k := by linarith
  have hD : (finalHessian S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ k) (S.L ^ k)
      (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2)
      (C.weights k) (fun i => hv i)).PosDef := by
    have hsym := finalHessian_transpose hℓ hN hd hν.le ha0 (h := fun i => hv i) he
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hsym
    · have hgap := finalHessian_form_ge_mass hℓ hN hd hν.le hν1 ha (h := fun i => hv i) he x
      have hxx : 0 < x ⬝ᵥ x := by
        obtain ⟨y, hy⟩ := Function.ne_iff.mp hx
        refine lt_of_lt_of_le (mul_self_pos.2 hy) ?_
        exact Finset.single_le_sum (f := fun y => x y * x y) (fun _ _ => mul_self_nonneg _)
          (Finset.mem_univ y)
      have hc : 0 < 1 / (8 * (S.d : ℝ) + 3) * (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) := by
        positivity
      simpa using lt_of_lt_of_le (mul_pos hc hxx) hgap
  refine (hD.smul hβ).submatrix ?_
  intro p q hpq
  simp only [Prod.mk.injEq] at hpq
  exact Prod.ext (torusCast_injective _ hpq.1) hpq.2

end Balaban.RootFSpine
