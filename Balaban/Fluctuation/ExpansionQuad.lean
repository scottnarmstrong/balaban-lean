module

public import Balaban.Fluctuation.Expansion
public import Balaban.Fluctuation.ExpansionDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Lemma 2.3 (b): the quadratic part and the interaction

For `ψ = ψ^{(k)} + ψ'` the exact expansion (2.4):
`J_k(θ, ψ) = A^η_{k+1}(θ, φ_{k+1}) + ½ a₁ L^{-2(n+1)} ‖Qψ'‖² + ½⟨ψ', Δ^{(k)} ψ'⟩ + V^{(k)}(ψ')`
with `Δ^{(k)} = a_k - a_k² Q_k (G_k - Π_k) Q_k^*` (`deltaForm`) and
`V^{(k)}(ψ') = ½⟨α^{(1)}, φ'·φ'⟩ + ½⟨φ₂, H_k φ₂⟩` (`interactionV`), where `H_k = opHk`,
`G_k = H_k⁻¹`, `Π_k = constrainedOp G_k φ_{k+1}` (GR (1.8′)), `(φ^{(1)}, α^{(1)})` the linear
response to the data tangent `S = a_k Q_k^* ψ'` (`phiOne`, `alphaOne`; BG Proposition 5.4),
`φ₂ = φ' - φ^{(1)}`.

* `linResp_facts`: `(φ^{(1)}, α^{(1)})` solves the linearised system `H φ¹ + α¹ φ = S`, `φ · φ¹ = 0`;
* `quad_algebra`: the algebra of the decomposition `φ' = φ¹ + φ₂`;
* `base_standing`: the standing hypotheses of the constrained operator at the base point
  (for `(θ, h)` with `δ ≤ thm73C2`);
* `expansion_quadratic` (Lemma 2.3 (b));
* on a region pair (`RegionPair`, P5 (2.21)–(2.22)): `levelEnergyCOn_expand_set` (the level energy on a
  set of sites of one layer, core of `levelEnergyC_expand`), `RegionPair.hess_compare` (the Hessians of
  `G'` and of `G` differ by their block terms on the new region), `base_standing_of` (core of
  `base_standing`), `RegionPair.expansion_quadratic_on` (core of `expansion_quadratic`: `ψ'` supported in
  the new region, `Δ^{(k)}`, `V^{(k)}` of the operator of `G` with all its layers).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Finset Matrix

section MatrixAlg

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem liftOp_transpose' (A : Matrix ι ι ℂ) : (liftOp N A)ᵀ = liftOp N Aᵀ := by
  ext p q
  simp only [transpose_apply, liftOp]
  by_cases h : p.2 = q.2
  · simp [h]
  · have h' : ¬ q.2 = p.2 := fun e => h e.symm
    simp [h, h']

/-- The linearised Euler--Lagrange system is solved by `φ¹ = (G - Π) S`, `α¹ = [φ·Gφ]⁻¹ φ·G S`
(the converse of `response_solve`): `H φ¹ + α¹ φ = S` and `φ · φ¹ = 0`. -/
theorem linResp_facts {H A : Matrix ι ι ℂ} (hHA : H * A = 1) {φ : ι → Fin N → ℂ}
    (hM : IsUnit (constraintForm A φ)) (S : ι × Fin N → ℂ) :
    liftOp N H *ᵥ ((liftOp N A - constrainedOp A φ) *ᵥ S) +
        fieldMul φ *ᵥ ((constraintForm A φ)⁻¹ *ᵥ
          ((fieldMul φ)ᵀ *ᵥ (liftOp N A *ᵥ S))) = S ∧
      (fieldMul φ)ᵀ *ᵥ ((liftOp N A - constrainedOp A φ) *ᵥ S) = 0 := by
  have h2 : liftOp N H * liftOp N A = 1 := by rw [← liftOp_mul, hHA, liftOp_one]
  have hMi : constraintForm A φ * (constraintForm A φ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hM)
  constructor
  · have hmat : liftOp N H * (liftOp N A - constrainedOp A φ) =
        1 - fieldMul φ * (constraintForm A φ)⁻¹ * (fieldMul φ)ᵀ * liftOp N A := by
      unfold constrainedOp
      simp only [Matrix.mul_sub, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.mulVec_mulVec, hmat]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    abel
  · have hmat : (fieldMul φ)ᵀ * (liftOp N A - constrainedOp A φ) = 0 := by
      unfold constrainedOp
      unfold constraintForm at hMi ⊢
      simp only [Matrix.mul_sub, ← Matrix.mul_assoc]
      rw [hMi]
      simp
    rw [Matrix.mulVec_mulVec, hmat, Matrix.zero_mulVec]

end MatrixAlg

section Pairs

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {N : ℕ}
variable {G : GeneratingSet d L N₀ K ϱ}

/-- `H_D(α)` is (complex) symmetric. -/
theorem dirichletOperator_transpose (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) :
    (dirichletOperator G a ν α)ᵀ = dirichletOperator G a ν α := by
  unfold dirichletOperator
  rw [transpose_add, diagonal_transpose]
  congr 1
  ext x y
  have := congrFun (congrFun (fullMatrix_transpose G a ν) y) x
  simp only [transpose_apply] at this
  simp [Green.restrictOp, this]

theorem pair_comm (u v : G.Ω 1 × Fin N → ℂ) : pair G u v = pair G v u := by
  unfold pair
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

theorem pair_add_left (u v w : G.Ω 1 × Fin N → ℂ) : pair G (u + v) w = pair G u w + pair G v w := by
  rw [pair_comm, pair_add_right, pair_comm, pair_comm w]

theorem pair_sub_left (u v w : G.Ω 1 × Fin N → ℂ) : pair G (u - v) w = pair G u w - pair G v w := by
  rw [pair_comm, pair_sub_right, pair_comm, pair_comm w]

/-- A complex-symmetric operator can be moved across the bilinear pairing. -/
theorem pair_mulVec_symm {H : Matrix (G.Ω 1) (G.Ω 1) ℂ} (hH : Hᵀ = H)
    (u v : G.Ω 1 × Fin N → ℂ) :
    pair G u (liftOp N H *ᵥ v) = pair G (liftOp N H *ᵥ u) v := by
  have e : ∀ x y : G.Ω 1 × Fin N → ℂ, pair G x y = x ⬝ᵥ y := fun x y => rfl
  rw [e, e, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, liftOp_transpose', hH]

theorem pair_fieldMul (u : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) (φ : G.Ω 1 → Fin N → ℂ) :
    pair G u (fieldMul φ *ᵥ α) = ∑ x, α x * ((fieldMul φ)ᵀ *ᵥ u) x := by
  unfold pair
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [fieldMul_transpose_mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fieldMul_mulVec]
  ring

/-- The algebra of the quadratic part: for `φ' = φ¹ + φ²` with `φ¹` solving the linearised system,
`½ ⟨φ', H φ'⟩ - ⟨φ', S⟩ = -½ ⟨S, φ¹⟩ + ½ ⟨α¹, φ'·φ'⟩ + ½ ⟨φ², H φ²⟩`. -/
theorem quad_algebra {H : Matrix (G.Ω 1) (G.Ω 1) ℂ} (hH : Hᵀ = H) {φb : G.Ω 1 → Fin N → ℂ}
    {Sd φ1 φ2 φ' : G.Ω 1 × Fin N → ℂ} {α1 : G.Ω 1 → ℂ}
    (E1 : liftOp N H *ᵥ φ1 + fieldMul φb *ᵥ α1 = Sd) (E2 : (fieldMul φb)ᵀ *ᵥ φ1 = 0)
    (hφ' : φ' = φ1 + φ2)
    (hcon : ∀ x, ∑ i, φb x i * φ' (x, i) = -(1 / 2) * ∑ i, φ' (x, i) * φ' (x, i)) :
    (1 / 2) * pair G φ' (liftOp N H *ᵥ φ') - pair G φ' Sd =
      -(1 / 2) * pair G Sd φ1 + (1 / 2) * ∑ x, α1 x * ∑ i, φ' (x, i) * φ' (x, i) +
        (1 / 2) * pair G φ2 (liftOp N H *ᵥ φ2) := by
  have hHφ1 : liftOp N H *ᵥ φ1 = Sd - fieldMul φb *ᵥ α1 := by rw [← E1]; abel
  have h1 : pair G φ1 (fieldMul φb *ᵥ α1) = 0 := by
    rw [pair_fieldMul, E2]; simp
  have h2 : pair G φ2 (fieldMul φb *ᵥ α1) =
      -(1 / 2) * ∑ x, α1 x * ∑ i, φ' (x, i) * φ' (x, i) := by
    rw [pair_fieldMul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e : ((fieldMul φb)ᵀ *ᵥ φ2) x = ∑ i, φb x i * φ' (x, i) := by
      have h3 : (fieldMul φb)ᵀ *ᵥ φ' = (fieldMul φb)ᵀ *ᵥ φ1 + (fieldMul φb)ᵀ *ᵥ φ2 := by
        rw [hφ', Matrix.mulVec_add]
      have h4 := congrFun h3 x
      rw [E2, fieldMul_transpose_mulVec] at h4
      simpa using h4.symm
    rw [e, hcon x]; ring
  have hsym : pair G φ1 (liftOp N H *ᵥ φ2) = pair G φ2 (liftOp N H *ᵥ φ1) := by
    rw [pair_mulVec_symm hH, pair_comm]
  have e1 : pair G φ' (liftOp N H *ᵥ φ') = pair G φ1 Sd - pair G φ1 (fieldMul φb *ᵥ α1) +
      2 * (pair G φ2 Sd - pair G φ2 (fieldMul φb *ᵥ α1)) + pair G φ2 (liftOp N H *ᵥ φ2) := by
    rw [hφ', Matrix.mulVec_add, pair_add_left]
    simp only [pair_add_right]
    rw [hsym, hHφ1]
    simp only [pair_sub_right]
    ring
  have e2 : pair G φ' Sd = pair G φ1 Sd + pair G φ2 Sd := by
    rw [hφ', pair_add_left]
  rw [e1, e2, h1, h2, pair_comm Sd φ1]
  ring

end Pairs

section Level

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ} {N : ℕ}
variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'} {n : ℕ}

/-- **The level energy on a set of sites of the layer `n`, expanded** (core of `levelEnergyC_expand` and
of `RegionPair.levelEnergyCOn_expand`): for a set `S ⊆ Ω₁` of sites of the layer `n` of `G` and a field
`ψ'` vanishing on `Ω₁ ∖ S` and constant on the blocks of the layers of `G`,
`level_{S,n}(ψ', φ') = ½ ⟨ψ', Q* a ψ'⟩ - ⟨φ', Q* a ψ'⟩ + level_{S,n}(0, φ')`. -/
theorem levelEnergyCOn_expand_set (S : Finset (Torus d (N₀ * L ^ K))) (hS : S ⊆ G.Ω 1)
    (hSl : ∀ x ∈ S, G.layerIndex x = n) (a : ℕ → ℝ) (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (hψ0 : ∀ x ∈ G.Ω 1, x ∉ S → ∀ i, ψ' x i = 0)
    (hψ : ∀ i, ∀ x ∈ G.Ω 1, ∀ y ∈ G.blk (G.layerIndex x) x, ψ' y i = ψ' x i)
    (φ' : G.Ω 1 × Fin N → ℂ) :
    levelEnergyCOn S G a n ψ' (svec G φ') =
      (1 / 2) * pair G (fun p => ψ' p.1 p.2) (qStar G a ψ') - pair G φ' (qStar G a ψ') +
        levelEnergyCOn S G a n (fun _ _ => 0) (svec G φ') := by
  have hsum : ∀ F : Torus d (N₀ * L ^ K) → ℂ, (∀ x ∈ G.Ω 1, x ∉ S → F x = 0) →
      ∑ x : G.Ω 1, F x = ∑ x ∈ S, F x := fun F hF => by
    rw [Finset.sum_coe_sort (G.Ω 1) F, ← Finset.sum_sdiff hS,
      Finset.sum_eq_zero fun x hx => hF x (Finset.mem_sdiff.1 hx).1 (Finset.mem_sdiff.1 hx).2,
      zero_add]
  have eC := sum_blockAvg (a := a) (g := fun i y => ψ' y i) hψ φ'
  have hb : ∀ x ∈ S, ∀ i, blockAvg G φ' x i = blockMean G n (fun y => svec G φ' y i) x :=
    fun x hx i => by
      unfold blockAvg blockMean
      rw [hSl x hx]
  have T1 : pair G (fun p => ψ' p.1 p.2) (qStar G a ψ') =
      ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) * ∑ x ∈ S, ∑ i, ψ' x i * ψ' x i := by
    have e : pair G (fun p => ψ' p.1 p.2) (qStar G a ψ') = ∑ x : G.Ω 1, ∑ i, ψ' x i *
        (((a (G.layerIndex (x : Torus d (N₀ * L ^ K))) /
          ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2 : ℝ) : ℂ) * ψ' x i) := by
      unfold pair qStar
      rw [Fintype.sum_prod_type]
    rw [e, hsum (fun x => ∑ i, ψ' x i * (((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
      ψ' x i)) (fun x hx hxR => Finset.sum_eq_zero fun i _ => by rw [hψ0 x hx hxR i, zero_mul])]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hSl x hx]; ring
  have T2 : pair G φ' (qStar G a ψ') =
      ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) *
        ∑ x ∈ S, ∑ i, ψ' x i * blockMean G n (fun y => svec G φ' y i) x := by
    have e : pair G φ' (qStar G a ψ') = ∑ p : G.Ω 1 × Fin N,
        ((a (G.layerIndex (p.1 : Torus d (N₀ * L ^ K))) /
          ((L : ℝ) ^ G.layerIndex (p.1 : Torus d (N₀ * L ^ K))) ^ 2 : ℝ) : ℂ) * ψ' p.1 p.2 * φ' p := by
      unfold pair
      exact Finset.sum_congr rfl fun p _ => by
        show φ' p * (((a (G.layerIndex p.1) / ((L : ℝ) ^ G.layerIndex p.1) ^ 2 : ℝ) : ℂ) *
          ψ' p.1 p.2) = _
        ring
    rw [e, ← eC]
    rw [hsum (fun x => ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
      ∑ i, ψ' x i * blockAvg G φ' x i) (fun x hx hxR => by
        simp only [hψ0 x hx hxR, zero_mul, Finset.sum_const_zero, mul_zero])]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hSl x hx]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hb x hx i]
  unfold levelEnergyCOn
  rw [T1, T2]
  have e3 : ∀ x i, (ψ' x i - blockMean G n (fun y => svec G φ' y i) x) *
      (ψ' x i - blockMean G n (fun y => svec G φ' y i) x) =
      ψ' x i * ψ' x i - 2 * (ψ' x i * blockMean G n (fun y => svec G φ' y i) x) +
        (0 - blockMean G n (fun y => svec G φ' y i) x) *
          (0 - blockMean G n (fun y => svec G φ' y i) x) := fun x i => by ring
  simp only [e3, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  push_cast
  ring

theorem levelEnergyC_expand (hG : IsLevel G n) (a : ℕ → ℝ) (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (hψ : ∀ i, ∀ x ∈ G.Ω 1, ∀ y ∈ G.blk (G.layerIndex x) x, ψ' y i = ψ' x i)
    (φ' : G.Ω 1 × Fin N → ℂ) :
    levelEnergyC G a n ψ' (svec G φ') =
      (1 / 2) * pair G (fun p => ψ' p.1 p.2) (qStar G a ψ') - pair G φ' (qStar G a ψ') +
        levelEnergyC G a n (fun _ _ => 0) (svec G φ') :=
  levelEnergyCOn_expand_set Finset.univ (fun x _ => (hG x).1) (fun x _ => (hG x).2) a ψ'
    (fun x _ hx => absurd (Finset.mem_univ x) hx) hψ φ'

theorem hessForm_restrict {n : ℕ} (hG : IsLevel G n) (hG' : IsLevel G' (n + 1)) (hp : n + 1 ≤ K)
    (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) (f : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    hessForm G' ν α₁ f = hessForm G ν ((hG.precedes hG' hp).restrictα α₁) f := by
  unfold hessForm
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  have h1 : x ∈ G.Ω 1 := (hG x).1
  have h2 : x ∈ G'.Ω 1 := (hG' x).1
  rw [zeroExt_mem _ _ ⟨x, h2⟩, zeroExt_mem _ _ ⟨x, h1⟩]
  rfl

theorem restrictField_barField (Ψ : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (φ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) (i : Fin N) :
    restrictField G (fun y j => barField G Ψ φ y j) x i = φ (x, i) := by
  simp [restrictField, barField]

/-- The tangent `ψ'` vanishes on `Ω₁` off the new region (the layers of `G` and `G'` agree there and
`D = D'`). -/
theorem RegionPair.compTangentOn_eq_zero (P : RegionPair G G' n)
    (a : ℕ → ℝ) (φ₁ : G'.Ω 1 × Fin N → ℂ) (D' : BgData G' N)
    (D : BgData G N) (hΨ : ∀ x, x ∉ G'.Ω (n + 1) → D.Ψ x = D'.Ψ x) {x : Torus d (N₀ * L ^ K)}
    (hx : x ∈ G.Ω 1) (hxR : x ∉ G'.Ω (n + 1)) (ha : a (G.layerIndex x) ≠ 0) (i : Fin N) :
    P.compTangentOn a φ₁ D' D x i = 0 := by
  unfold compTangentOn
  show D.Ψ x i - composeField G G' a φ₁ D'.Ψ x i = 0
  rw [composeField_of_mem a φ₁ D'.Ψ hx i, P.off_layer x hx hxR, hΨ x hxR]
  have hL : ((L : ℝ) ^ G.layerIndex x) ^ 2 ≠ 0 := by
    have : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    positivity
  have h1 : ((a (G.layerIndex x) / a (G.layerIndex x) *
      (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G.layerIndex x) ^ 2) : ℝ) : ℂ) = 1 := by
    rw [div_self ha, div_self hL]; simp
  rw [h1]
  have hb : blockMean G (G.layerIndex x) (fun y => svec G' φ₁ y i) x =
      blockMean G' (G.layerIndex x) (fun y => svec G' φ₁ y i) x := rfl
  rw [hb]
  ring

/-- The tangent `ψ'` is constant on the blocks of the layers of `G`. -/
theorem RegionPair.compTangentOn_blockConst (P : RegionPair G G' n)
    (a : ℕ → ℝ) (φ₁ : G'.Ω 1 × Fin N → ℂ) (D' : BgData G' N)
    (D : BgData G N) (i : Fin N) :
    ∀ x ∈ G.Ω 1, ∀ y ∈ G.blk (G.layerIndex x) x,
      P.compTangentOn a φ₁ D' D y i = P.compTangentOn a φ₁ D' D x i := by
  intro x hx y hy
  obtain ⟨hm1, hmk, hxl⟩ := G.layerIndex_spec hx
  have h1 := congrFun (D.Ψ_layerConst _ hm1 hmk x hxl y hy) i
  have h2 := congrFun ((composeData P.hpre a φ₁ D').Ψ_layerConst _ hm1 hmk x hxl y hy) i
  unfold compTangentOn
  rw [h1, h2]

/-- **The level energy on the new region, expanded** (region form of `levelEnergyC_expand`): for a
field `ψ'` vanishing on `Ω₁` off `R = Ω'_{n+1}` and constant on the blocks of the layers of `G`,
`level_{R,n}(ψ', φ') = ½ ⟨ψ', Q* a ψ'⟩ - ⟨φ', Q* a ψ'⟩ + level_{R,n}(0, φ')`. -/
theorem RegionPair.levelEnergyCOn_expand (P : RegionPair G G' n) (a : ℕ → ℝ)
    (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (hψ0 : ∀ x ∈ G.Ω 1, x ∉ G'.Ω (n + 1) → ∀ i, ψ' x i = 0)
    (hψ : ∀ i, ∀ x ∈ G.Ω 1, ∀ y ∈ G.blk (G.layerIndex x) x, ψ' y i = ψ' x i)
    (φ' : G.Ω 1 × Fin N → ℂ) :
    levelEnergyCOn (G'.Ω (n + 1)) G a n ψ' (svec G φ') =
      (1 / 2) * pair G (fun p => ψ' p.1 p.2) (qStar G a ψ') - pair G φ' (qStar G a ψ') +
        levelEnergyCOn (G'.Ω (n + 1)) G a n (fun _ _ => 0) (svec G φ') :=
  levelEnergyCOn_expand_set (G'.Ω (n + 1)) P.top_subset (fun x hx => (P.top_layer x hx).1) a ψ' hψ0 hψ φ'

/-- `liftφ` of `φ - restrictφ φ₁` is `liftφ φ - φ₁`. -/
theorem RegionPair.liftφ_sub_restrictφ (P : RegionPair G G' n)
    (φ : G.Ω 1 × Fin N → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ) :
    P.liftφ (φ - P.hpre.restrictφ φ₁) = P.liftφ φ - φ₁ := by
  funext q
  rfl

/-- The extensions of `liftφ φ` and of `φ` to the torus agree. -/
theorem RegionPair.svec_liftφ (P : RegionPair G G' n)
    (φ : G.Ω 1 × Fin N → ℂ) : svec G' (P.liftφ φ) = svec G φ := by
  funext y i
  by_cases hy : y ∈ G.Ω 1
  · have hy' : y ∈ G'.Ω 1 := P.Ω_one ▸ hy
    rw [svec_of_mem' (G' := G') _ hy' i, svec_of_mem' (G' := G) _ hy i]
    rfl
  · rw [svec_of_not_mem G' _ (P.Ω_one ▸ hy), svec_of_not_mem G _ hy]

/-- The bilinear product of the fields of `G'` and of `G` along `liftφ`. -/
theorem RegionPair.pair_liftφ (P : RegionPair G G' n)
    (φ : G.Ω 1 × Fin N → ℂ) (v : G'.Ω 1 × Fin N → ℂ) (w : G.Ω 1 × Fin N → ℂ)
    (hw : ∀ (x : G'.Ω 1) i, v (x, i) = w (⟨x.1, P.Ω_one ▸ x.2⟩, i)) :
    pair G' (P.liftφ φ) v = pair G φ w := by
  unfold pair
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight (fun x => by rw [P.Ω_one])) _ _
    (fun x => Finset.sum_congr rfl fun i _ => by rw [hw x i]; rfl)

/-- **The Hessian of the action of `G'` and that of `G` on a region pair**: for `φ'` on `Ω₁`,
`½ ⟨φ', H'(α) φ'⟩ - level'_{R,n+1}(0, φ') = ½ ⟨φ', H(α|) φ'⟩ - level_{R,n}(0, φ')`: the two operators
differ only by their block terms on the new region `R`, which are `2 level'_{R,n+1}(0, ·)` and
`2 level_{R,n}(0, ·)`. -/
theorem RegionPair.hess_compare (P : RegionPair G G' n)
    (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) (φ' : G.Ω 1 × Fin N → ℂ) :
    (1 / 2) * pair G' (P.liftφ φ') (liftOp N (dirichletOperator G' a ν α₁) *ᵥ P.liftφ φ') -
        levelEnergyCOn (G'.Ω (n + 1)) G' a (n + 1) (fun _ _ => 0) (svec G φ') =
      (1 / 2) * pair G φ' (liftOp N (dirichletOperator G a ν (P.hpre.restrictα α₁)) *ᵥ φ') -
        levelEnergyCOn (G'.Ω (n + 1)) G a n (fun _ _ => 0) (svec G φ') := by
  set R := G'.Ω (n + 1) with hRdef
  set τ := P.liftφ φ' with hτ
  have hsv : svec G' τ = svec G φ' := P.svec_liftφ φ'
  have dec' : pair G' τ (liftOp N (dirichletOperator G' a ν α₁) *ᵥ τ) =
      pair G' τ (lapVec G' τ) + pair G' τ (blockVec G' a τ) + (ν : ℂ) * pair G' τ τ +
        pair G' τ (fun p => α₁ p.1 * τ p) := by
    unfold pair
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [H_alpha_apply, H0_apply]
    ring
  have dec : pair G φ' (liftOp N (dirichletOperator G a ν (P.hpre.restrictα α₁)) *ᵥ φ') =
      pair G φ' (lapVec G φ') + pair G φ' (blockVec G a φ') + (ν : ℂ) * pair G φ' φ' +
        pair G φ' (fun p => P.hpre.restrictα α₁ p.1 * φ' p) := by
    unfold pair
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [H_alpha_apply, H0_apply]
    ring
  have hlap : pair G' τ (lapVec G' τ) = pair G φ' (lapVec G φ') := by
    rw [pair_lapVec_eq_bond, pair_lapVec_eq_bond, hsv]
  have hν : pair G' τ τ = pair G φ' φ' := P.pair_liftφ φ' τ φ' (fun _ _ => rfl)
  have hα : pair G' τ (fun p => α₁ p.1 * τ p) =
      pair G φ' (fun p => P.hpre.restrictα α₁ p.1 * φ' p) :=
    P.pair_liftφ φ' _ _ (fun _ _ => rfl)
  have hblk : pair G' τ (blockVec G' a τ) - 2 * levelEnergyCOn R G' a (n + 1) (fun _ _ => 0)
        (svec G φ') =
      pair G φ' (blockVec G a φ') - 2 * levelEnergyCOn R G a n (fun _ _ => 0) (svec G φ') := by
    rw [pair_blockVec_eq_sum, pair_blockVec_eq_sum]
    rw [Finset.sum_coe_sort (G'.Ω 1) (fun x => ((a (G'.layerIndex x) / ((L : ℝ) ^ G'.layerIndex x) ^ 2 : ℝ) : ℂ) *
        ∑ i, blockAvg G' τ x i * blockAvg G' τ x i),
      Finset.sum_coe_sort (G.Ω 1) (fun x => ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
        ∑ i, blockAvg G φ' x i * blockAvg G φ' x i), P.Ω_one,
      ← Finset.sum_sdiff P.top_subset, ← Finset.sum_sdiff P.top_subset]
    have hoff : ∑ x ∈ G.Ω 1 \ R, ((a (G'.layerIndex x) / ((L : ℝ) ^ G'.layerIndex x) ^ 2 : ℝ) : ℂ) *
          ∑ i, blockAvg G' τ x i * blockAvg G' τ x i =
        ∑ x ∈ G.Ω 1 \ R, ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
          ∑ i, blockAvg G φ' x i * blockAvg G φ' x i := by
      refine Finset.sum_congr rfl fun x hx => ?_
      obtain ⟨hx1, hxR⟩ := Finset.mem_sdiff.1 hx
      have hl := P.off_layer x hx1 hxR
      have hb : ∀ i, blockAvg G' τ x i = blockAvg G φ' x i := fun i => by
        unfold blockAvg
        rw [hl, hsv]
        rfl
      simp only [hl, hb]
    have hR' : ∑ x ∈ R, ((a (G'.layerIndex x) / ((L : ℝ) ^ G'.layerIndex x) ^ 2 : ℝ) : ℂ) *
          ∑ i, blockAvg G' τ x i * blockAvg G' τ x i =
        2 * levelEnergyCOn R G' a (n + 1) (fun _ _ => 0) (svec G φ') := by
      unfold levelEnergyCOn
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
      rw [(P.top_layer x hx).2]
      have hb : blockAvg G' τ x i = blockMean G' (n + 1) (fun y => svec G φ' y i) x := by
        unfold blockAvg blockMean
        rw [(P.top_layer x hx).2, hsv]
      rw [hb]
      push_cast
      ring
    have hR : ∑ x ∈ R, ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
          ∑ i, blockAvg G φ' x i * blockAvg G φ' x i =
        2 * levelEnergyCOn R G a n (fun _ _ => 0) (svec G φ') := by
      unfold levelEnergyCOn
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
      rw [(P.top_layer x hx).1]
      have hb : blockAvg G φ' x i = blockMean G n (fun y => svec G φ' y i) x := by
        unfold blockAvg blockMean
        rw [(P.top_layer x hx).1]
      rw [hb]
      push_cast
      ring
    rw [hoff, hR', hR]
    ring
  linear_combination (1 / 2 : ℂ) * dec' - (1 / 2 : ℂ) * dec + (1 / 2 : ℂ) * hlap +
    ((ν : ℂ) / 2) * hν + (1 / 2 : ℂ) * hα + (1 / 2 : ℂ) * hblk

end Level
section Quad

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ} {N : ℕ}
variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'} {a₁ ν : ℝ} {n : ℕ}

/-- The standing hypotheses of the constrained operator at the base point
`(ψ^{(k)}, φ_{k+1}|, α_{k+1}|)`, for `(θ, h)` in `𝒟(𝔹')` with `δ ≤ thm73C2`, for any pair `G ≺ G'`
(core of `base_standing`). -/
theorem base_standing_of (h : Precedes G G') (ha₁ : 0 < a₁) (H : BgHyp d L K ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L K ϱ' (compWeight L a₁) ν) (D' : BgData G' N)
    (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C2 d L N) ν D') :
    ∃ (δ : ℝ) (Φ : Torus d (N₀ * L ^ K) → Fin N → ℂ),
      Standing G (compWeight L a₁) ν
        (h.restrictα (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')) δ Φ ∧
      ∀ (x : G.Ω 1) i, restrictField G Φ x i =
        h.restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') (x, i) := by
  have hdom := theorem73_complex_small ha₁ H H' h hD'
  obtain ⟨-, hfield, hmult⟩ := theorem73_complex ha₁ H H' h
    (InUnionDomainC.mono (thm73C2_le_thm73C1 d L N) hD')
  obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hdom
  have St := standing_bgFieldC H hδ0 hδε hε hδc hνε hDC
  rw [hfield, hmult] at St
  refine ⟨_, _, St, fun x i => ?_⟩
  exact restrictField_barField _ _ x i

/-- The standing hypotheses of the constrained operator at the base point
`(ψ^{(k)}, φ_{k+1}|, α_{k+1}|)`, for `(θ, h)` in `𝒟(𝔹'_k)` with `δ ≤ thm73C2`. -/
theorem base_standing (ha₁ : 0 < a₁) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (H : BgHyp d L K ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L K ϱ' (compWeight L a₁) ν) (D' : BgData G' N)
    (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C2 d L N) ν D') :
    ∃ (δ : ℝ) (Φ : Torus d (N₀ * L ^ K) → Fin N → ℂ),
      Standing G (compWeight L a₁) ν
        ((hG.precedes hG' hp).restrictα (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')) δ Φ ∧
      ∀ (x : G.Ω 1) i, restrictField G Φ x i =
        (hG.precedes hG' hp).restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') (x, i) :=
  base_standing_of (hG.precedes hG' hp) ha₁ H H' D' hD'

/-- `H_k = -Δ + a_k Q_k^* Q_k + ν + α_{k+1}` on `Ω₁` (level `n`), `α_{k+1}` restricted. -/
noncomputable def opHk (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) :
    Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  dirichletOperator G a ν (h.restrictα α₁)

/-- The base field `φ_{k+1}` restricted to `Ω₁`, as a vector field. -/
noncomputable def fieldBase (h : Precedes G G') (φ₁ : G'.Ω 1 × Fin N → ℂ) :
    G.Ω 1 → Fin N → ℂ := fun x i => h.restrictφ φ₁ (x, i)

/-- The linear response `φ^{(1)} = (G_k - Π_k) S` for the data tangent `S = a_k Q_k^* ψ'`
(`G_k = H_k⁻¹`, `Π_k = constrainedOp G_k φ_{k+1}`, GR (1.8′), BG Proposition 5.4). -/
noncomputable def phiOne (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) (S : G.Ω 1 × Fin N → ℂ) : G.Ω 1 × Fin N → ℂ :=
  (liftOp N (opHk h a ν α₁)⁻¹ - constrainedOp (opHk h a ν α₁)⁻¹ (fieldBase h φ₁)) *ᵥ S

/-- The multiplier response `α^{(1)} = [φ_{k+1} · G_k φ_{k+1}]⁻¹ φ_{k+1} · G_k S`. -/
noncomputable def alphaOne (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) (S : G.Ω 1 × Fin N → ℂ) : G.Ω 1 → ℂ :=
  (constraintForm (opHk h a ν α₁)⁻¹ (fieldBase h φ₁))⁻¹ *ᵥ
    ((fieldMul (fieldBase h φ₁))ᵀ *ᵥ (liftOp N (opHk h a ν α₁)⁻¹ *ᵥ S))

/-- The quadratic form `⟨ψ', Δ^{(k)} ψ'⟩ = a_k ‖ψ'‖² - ⟨S, (G_k - Π_k) S⟩`, `S = a_k Q_k^* ψ'`, of
(2.4) (`Δ^{(k)} = a_k - a_k² Q_k (G_k - Π_k) Q_k^*`), in fine units. -/
noncomputable def deltaForm (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  pair G (fun p => ψ' p.1 p.2) (qStar G a ψ') -
    pair G (qStar G a ψ') (phiOne h a ν α₁ φ₁ (qStar G a ψ'))

/-- The interaction `V^{(k)}(ψ') = ½⟨α^{(1)}, φ'·φ'⟩ + ½⟨φ₂, H_k φ₂⟩` of (2.4), `φ₂ = φ' - φ^{(1)}`. -/
noncomputable def interactionV (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (φ' : G.Ω 1 × Fin N → ℂ) : ℂ :=
  (1 / 2) * ∑ x, alphaOne h a ν α₁ φ₁ (qStar G a ψ') x * ∑ i, φ' (x, i) * φ' (x, i) +
    (1 / 2) * pair G (φ' - phiOne h a ν α₁ φ₁ (qStar G a ψ'))
      (liftOp N (opHk h a ν α₁) *ᵥ (φ' - phiOne h a ν α₁ φ₁ (qStar G a ψ')))

/-- **Lemma 2.3 (b) on a region pair: the quadratic part and the interaction (2.4)** (P5 (2.21)–(2.22);
core of `expansion_quadratic`).  Under the hypotheses of `expansion_chord_on` (with `(θ, h)` in
`𝒟(𝔹')` for `δ ≤ thm73C2`), in the notation `h = P.hpre`, `ψ' = compTangentOn …` (supported in the new
region `R`), `S = a Q^* ψ'`, `φ' = φ_k(ψ) - φ_{k+1}|`:
`J_k(θ, ψ) = A'(θ, φ_{k+1}) + coupling_R(0, ψ') + ½ ⟨ψ', Δ^{(k)} ψ'⟩ + V^{(k)}(ψ')`,
with `Δ^{(k)}` (`deltaForm`) and `V^{(k)}` (`interactionV`) those of the operator
`H_k = -Δ + Q^* a Q + ν + α_{k+1}|` of `G` (all its layers). -/
theorem RegionPair.expansion_quadratic_on (P : RegionPair G G' n) (ha₁ : 0 < a₁)
    (H : BgHyp d L K ϱ (compWeight L a₁) ν) (H' : BgHyp d L K ϱ' (compWeight L a₁) ν)
    (D' : BgData G' N) (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C2 d L N) ν D')
    (D : BgData G N) (hh : ∀ x i, D.h x i = D'.h x i)
    (hΨ : ∀ x, x ∉ G'.Ω (n + 1) → D.Ψ x = D'.Ψ x)
    (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D) :
    couplingCOn (G'.Ω (n + 1)) G' a₁ (n + 1) D'.Ψ D.Ψ +
        actionC G (compWeight L a₁) ν D (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D) =
      actionC G' (compWeight L a₁) ν D' (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') +
        couplingCOn (G'.Ω (n + 1)) G' a₁ (n + 1) (fun _ _ => 0) (P.compTangentOn (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D) +
        (1 / 2) * deltaForm P.hpre (compWeight L a₁) ν
          (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (P.compTangentOn (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D) +
        interactionV P.hpre (compWeight L a₁) ν
          (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (P.compTangentOn (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D)
          (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D -
            P.hpre.restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hL2 : 2 ≤ L := by have := H.hL; omega
  have hD'1 : InUnionDomainC G' (bgC0 d L N) (thm73C1 d L N) ν D' :=
    InUnionDomainC.mono (thm73C2_le_thm73C1 d L N) hD'
  have hD'2 : InUnionDomainC G' (bgC0 d L N) (bgC1 d L N) ν D' := by
    obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hD'1
    exact ⟨δ, ε, hδ0, hδε, hε, (thm73_small (L := L) (N := N) hd0 hδ0 hδc).1, hνε, hDC⟩
  have chord := P.expansion_chord_on ha₁ H H' D' hD'1 D hh hΨ hD
  obtain ⟨δs, Φ, St, hΦ⟩ := base_standing_of P.hpre ha₁ H H' D' hD'
  set a := compWeight L a₁ with ha
  set h := P.hpre with hh'
  set φ₁ := bgFieldC G' a ν (bgC0 d L N) D' with hφ₁
  set α₁ := bgMultC G' a ν (bgC0 d L N) D' with hα₁
  set φD := bgFieldC G a ν (bgC0 d L N) D with hφD
  set ψ' := P.compTangentOn a φ₁ D' D with hψ'
  set φ' : G.Ω 1 × Fin N → ℂ := φD - h.restrictφ φ₁ with hφ'
  set Sd := qStar G a ψ' with hSd
  have hHu : IsUnit (opHk h a ν α₁) :=
    dirichletOperator_isUnit G St.pos St.mass St.weights _ St.alpha
  have hHA : opHk h a ν α₁ * (opHk h a ν α₁)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hHu)
  have hΦ' : restrictField G Φ = fieldBase h φ₁ := funext fun x => funext fun i => hΦ x i
  have hM : IsUnit (constraintForm (opHk h a ν α₁)⁻¹ (fieldBase h φ₁)) := by
    rw [← hΦ']; exact constraintForm_isUnit St
  obtain ⟨E1, E2⟩ := linResp_facts (N := N) hHA hM Sd
  have hψc : ∀ i, ∀ x ∈ G.Ω 1, ∀ y ∈ G.blk (G.layerIndex x) x, ψ' y i = ψ' x i :=
    fun i => P.compTangentOn_blockConst a φ₁ D' D i
  have hψ0 : ∀ x ∈ G.Ω 1, x ∉ G'.Ω (n + 1) → ∀ i, ψ' x i = 0 := fun x hx hxR i =>
    P.compTangentOn_eq_zero a φ₁ D' D hΨ hx hxR
      (compWeight_pos hL2 ha₁ (G.layerIndex_spec hx).1).ne' i
  have hφDc := (theorem72 H hD).2.1.1.2
  have hφ₁c := (theorem72 H' hD'2).2.1.1.2
  have hcon : ∀ x : G.Ω 1, ∑ i, fieldBase h φ₁ x i * φ' (x, i) =
      -(1 / 2) * ∑ i, φ' (x, i) * φ' (x, i) := fun x => by
    have e1 := hφDc x
    have e2 : ∑ i, fieldBase h φ₁ x i * fieldBase h φ₁ x i = 1 := hφ₁c (h.incl x)
    have e3 : ∑ i, φD (x, i) * φD (x, i) = ∑ i, fieldBase h φ₁ x i * fieldBase h φ₁ x i +
        2 * ∑ i, fieldBase h φ₁ x i * φ' (x, i) + ∑ i, φ' (x, i) * φ' (x, i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : φD (x, i) = fieldBase h φ₁ x i + φ' (x, i) := by
        simp only [hφ', Pi.sub_apply, fieldBase]; ring
      rw [this]; ring
    linear_combination (1 / 2 : ℂ) * e1 - (1 / 2 : ℂ) * e2 - (1 / 2 : ℂ) * e3
  have lev := P.levelEnergyCOn_expand a ψ' hψ0 hψc φ'
  have hc := P.hess_compare a ν α₁ φ'
  rw [← P.liftφ_sub_restrictφ] at chord
  have qa := quad_algebra (G := G) (H := opHk h a ν α₁)
    (dirichletOperator_transpose a ν _) (φb := fieldBase h φ₁) (Sd := Sd)
    (φ1 := phiOne h a ν α₁ φ₁ Sd) (φ2 := φ' - phiOne h a ν α₁ φ₁ Sd) (φ' := φ')
    (α1 := alphaOne h a ν α₁ φ₁ Sd) E1 E2 (by abel) hcon
  unfold deltaForm interactionV
  rw [← hSd]
  unfold opHk at qa ⊢
  linear_combination chord + lev + hc + qa

/-- **Lemma 2.3 (b): the quadratic part and the interaction (2.4).**  Under the hypotheses of
`expansion_chord` (with `(θ, h)` in `𝒟(𝔹'_k)` for `δ ≤ thm73C2`, so that the constrained operator
`Π_k` of the base point is defined), in the notation `h = hG.precedes hG' hp`,
`S = a_k Q_k^* ψ'`, `φ' = φ_k(ψ) - φ_{k+1}|`:
`J_k(θ, ψ) = A^η_{k+1}(θ, φ_{k+1}) + ½ a₁ L^{-2(n+1)} ‖Qψ'‖² + ½ ⟨ψ', Δ^{(k)} ψ'⟩ + V^{(k)}(ψ')`,
with `Δ^{(k)}` the form `deltaForm` and `V^{(k)}` the interaction `interactionV`. -/
theorem expansion_quadratic (ha₁ : 0 < a₁) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (H : BgHyp d L K ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L K ϱ' (compWeight L a₁) ν) (D' : BgData G' N)
    (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C2 d L N) ν D') (D : BgData G N)
    (hh : ∀ x i, D.h x i = D'.h x i)
    (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D) :
    couplingC G' a₁ (n + 1) D'.Ψ D.Ψ +
        actionC G (compWeight L a₁) ν D (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D) =
      actionC G' (compWeight L a₁) ν D' (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') +
        couplingC G' a₁ (n + 1) (fun _ _ => 0) (compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D) +
        (1 / 2) * deltaForm (hG.precedes hG' hp) (compWeight L a₁) ν
          (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (compTangent hG hG' hp (compWeight L a₁)
            (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D) +
        interactionV (hG.precedes hG' hp) (compWeight L a₁) ν
          (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (compTangent hG hG' hp (compWeight L a₁)
            (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D)
          (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D -
            (hG.precedes hG' hp).restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')) := by
  have h := (RegionPair.ofLevel hG hG' hp).expansion_quadratic_on ha₁ H H' D' hD' D hh
    (fun x hx => absurd (hG'.Ω_top ▸ Finset.mem_univ x) hx) hD
  rw [hG'.Ω_top] at h
  exact h

end Quad

end Balaban.Fluctuation
