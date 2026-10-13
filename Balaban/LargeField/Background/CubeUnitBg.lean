module

public import Balaban.LargeField.Characteristic.Functions
public import Balaban.LargeField.Characteristic.RealDomain
public import Balaban.LargeField.Background.Factorization
public import Balaban.Multiscale.ConstraintKernel
public import Balaban.Background.CompositionSystem
public import Balaban.LargeField.R.ChiBridge
public import Balaban.LargeField.Def7SmallField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The constant unit datum on a general generating set; `Reg` and `χ_k` at the constant field

For a generating set `G` (any level structure, not necessarily the whole lattice), a real unit
vector `e ∈ ℝ^N` (`∑ eᵢ² = 1`), the *constant datum* is `Ψ ≡ e` on `Ω₁ ∪ C(Ω₁)`, `h̃ ≡ e` on
`Ω₁` (`constUnitBg`), and the *constant field* is `φ ≡ e` on `Ω₁` (`constUnitPhi`).

## General lemmas (hypotheses: `BgHyp`, typing)

* `constUnitBg_inDomainR`: the constant datum lies in `Ψ̃(G; r)` for every mass and every radius
  `r > 0` (differences vanish, `|e|² = 1`, `e · e / |e| = 1`); `constUnitBg_inUnionDomainR`: it lies
  in `𝒟_ℝ(G)` under `BgHyp`.
* `action_constUnitBg_eq_zero`: the constant field has action `0` (every term vanishes: `Ψ = Qφ`
  because block averages of a constant are the constant, `φ̄` is constant on the bonds seen by the
  action, `φ = h̃`); `isMinimizer_constUnitBg`: it is a minimizer, since the action is nonnegative.
* `dirichlet_const_eq_source`: `H_D(0) φ = S(Ψ, h̃)` for the constant field, so the multiplier is
  `0` (the rows of `-Δ + ν + Q* a Q` restricted to `Ω₁` sum to `ν + #missing neighbours + a_n L^{-2n}`,
  and the collar neighbours put exactly `e` per missing neighbour into the source).
* `bgField_constUnitBg`, `bgMult_constUnitBg`, `bgFieldC_constUnitBg`, `bgMultC_constUnitBg`:
  by the uniqueness of the minimizer in `𝒟_ℝ` (`theorem71`) and `theorem72_real`, the Def-5
  background of the constant datum is the constant field, with multiplier `0`.

Only `BgHyp` is used: `3 ≤ d` (for `c₁ > 0`), admissible weights (for the nonnegativity of the
action on the layers), `0 ≤ ν`; no `IsLevel`, no `ν = 0`.

## Cube and small-field level

* `reg_cubeData_const`: for the cube generating set `genCube y0` and `cubeData e y0 (ψ ≡ e)`,
  `Reg` holds for every `δ > 0` (the neighbourhood `□^{∼1}` lies in `Ω₁`);
  `chiK_const_eq_one`: `χ_q(□) = 1`.
* `chiY_const_eq_one`: for an `SFCtx` with `δ_k > 0` and the cube `BgHyp`, `χ_k(Y) = 1` for every
  `Y`, at the constant block field.

These tests exercise the single-scale small-field branch at a constant field only; they say nothing
about non-constant fields or the retained large-field components.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Matrix

set_option linter.unusedSectionVars false

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Const

variable (G : GeneratingSet d L N₀ K ϱ)

/-- The constant field `φ ≡ e` on `Ω₁` (a unit vector of `ℝ^N` at each site when `|e| = 1`). -/
noncomputable def constUnitPhi (e : Fin N → ℝ) : G.Ω 1 × Fin N → ℂ := fun p => (e p.2 : ℂ)

/-- The constant datum `Ψ ≡ e` on the data sites `Ω₁ ∪ C(Ω₁)`, `h̃ ≡ e` on `Ω₁` (zero elsewhere). -/
noncomputable def constUnitBg (e : Fin N → ℝ) : BgData G N :=
  BgData.clip G (fun _ i => (e i : ℂ)) (fun _ i => (e i : ℂ))
    (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)

variable {G}

theorem constUnitBg_Ψ {e : Fin N → ℝ} {x : Torus d (N₀ * L ^ K)} (hx : x ∈ dataSites G)
    (i : Fin N) : (constUnitBg G e).Ψ x i = (e i : ℂ) := by
  simp [constUnitBg, BgData.clip, hx]

theorem constUnitBg_h {e : Fin N → ℝ} {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1)
    (i : Fin N) : (constUnitBg G e).h x i = (e i : ℂ) := by
  simp [constUnitBg, BgData.clip, hx]

theorem svec_constUnitPhi (e : Fin N → ℝ) {y : Torus d (N₀ * L ^ K)} (hy : y ∈ G.Ω 1) (i : Fin N) :
    svec G (constUnitPhi G e) y i = (e i : ℂ) := by
  rw [svec_of_mem G _ ⟨y, hy⟩ i]
  rfl

theorem blockAvg_constUnitPhi (e : Fin N → ℝ) {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1)
    (i : Fin N) : blockAvg G (constUnitPhi G e) x i = (e i : ℂ) := by
  obtain ⟨h1, h2, h3⟩ := G.layerIndex_spec hx
  have hsub := blk_subset_Ω G h1 h2 h3
  have : blockAvg G (constUnitPhi G e) x i =
      blockMean G (G.layerIndex x) (fun _ => (e i : ℂ)) x := by
    unfold blockAvg blockMean
    congr 1
    exact Finset.sum_congr rfl fun y hy => svec_constUnitPhi e (hsub hy) i
  rw [this]
  exact blockMean_const G h2 _ x

theorem barField_constUnitPhi (e : Fin N → ℝ) {y : Torus d (N₀ * L ^ K)} (hy : y ∈ dataSites G)
    (i : Fin N) : barField G (constUnitBg G e).Ψ (constUnitPhi G e) y i = (e i : ℂ) := by
  by_cases h : y ∈ G.Ω 1
  · simp [barField, h, constUnitPhi]
  · simp [barField, h, constUnitBg_Ψ hy]


theorem mem_dataSites_of_adj {x : Torus d (N₀ * L ^ K)} (μ : Fin d)
    (h : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1) :
    x ∈ dataSites G ∧ x + Pi.single μ 1 ∈ dataSites G := by
  rcases h with h | h
  · refine ⟨(mem_dataSites G).2 (Or.inl h), (mem_dataSites G).2 ?_⟩
    by_cases h' : x + Pi.single μ 1 ∈ G.Ω 1
    · exact Or.inl h'
    · exact Or.inr (mem_collar_of_adj G h h' ⟨μ, Or.inl rfl⟩)
  · refine ⟨(mem_dataSites G).2 ?_, (mem_dataSites G).2 (Or.inl h)⟩
    by_cases h' : x ∈ G.Ω 1
    · exact Or.inl h'
    · exact Or.inr (mem_collar_of_adj G h h' ⟨μ, Or.inr rfl⟩)

theorem mem_dataSites_sub {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1) (μ : Fin d) :
    x - Pi.single μ 1 ∈ dataSites G := by
  refine (mem_dataSites G).2 ?_
  by_cases h' : x - Pi.single μ 1 ∈ G.Ω 1
  · exact Or.inl h'
  · exact Or.inr (mem_collar_of_adj G hx h' ⟨μ, Or.inr (sub_add_cancel x _).symm⟩)

theorem mem_dataSites_add {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1) (μ : Fin d) :
    x + Pi.single μ 1 ∈ dataSites G := (mem_dataSites_of_adj μ (Or.inl hx)).2

/-- **The constant field has action zero** for the constant datum, for every generating set,
weights and mass. -/
theorem action_constUnitBg_eq_zero (e : Fin N → ℝ) (a : ℕ → ℝ) (ν : ℝ) :
    action G a ν (constUnitBg G e) (constUnitPhi G e) = 0 := by
  unfold action
  have h1 : ∀ x : G.Ω 1, ∀ i,
      (constUnitBg G e).Ψ x i - blockAvg G (constUnitPhi G e) x i = 0 := by
    intro x i
    rw [blockAvg_constUnitPhi e x.2, constUnitBg_Ψ ((mem_dataSites G).2 (Or.inl x.2)), sub_self]
  have h2 : ∀ (x : Torus d (N₀ * L ^ K)) (μ : Fin d),
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, ‖barField G (constUnitBg G e).Ψ (constUnitPhi G e) (x + Pi.single μ 1) i -
          barField G (constUnitBg G e).Ψ (constUnitPhi G e) x i‖ ^ 2 else 0) = 0 := by
    intro x μ
    split_ifs with h
    · obtain ⟨hx, hx'⟩ := mem_dataSites_of_adj μ h
      simp [barField_constUnitPhi e hx, barField_constUnitPhi e hx']
    · rfl
  have h3 : ∀ x : G.Ω 1, ∑ i, ‖constUnitPhi G e (x, i) - (constUnitBg G e).h x i‖ ^ 2 = 0 := by
    intro x
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [constUnitBg_h x.2]
    simp [constUnitPhi]
  simp [h1, h2, h3]

/-- The action is nonnegative when the weights on the layers `1..K` and the mass are. -/
theorem action_nonneg_layers {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ n → n ≤ K → 0 ≤ a n) {ν : ℝ}
    (hν : 0 ≤ ν) (D : BgData G N) (σ : G.Ω 1 × Fin N → ℂ) : 0 ≤ action G a ν D σ := by
  unfold action
  have t1 : 0 ≤ (1 / 2 : ℝ) * ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ K))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2) *
      ∑ i, ‖D.Ψ x i - blockAvg G σ x i‖ ^ 2 := by
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => mul_nonneg ?_ ?_)
    · obtain ⟨h1, h2, -⟩ := G.layerIndex_spec x.2
      exact div_nonneg (ha _ h1 h2) (by positivity)
    · exact Finset.sum_nonneg fun i _ => by positivity
  have t2 : 0 ≤ (1 / 2 : ℝ) * ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, ‖barField G D.Ψ σ (x + Pi.single μ 1) i - barField G D.Ψ σ x i‖ ^ 2 else 0) := by
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ => ?_)
    split_ifs
    · exact Finset.sum_nonneg fun i _ => by positivity
    · exact le_rfl
  have t3 : 0 ≤ ν / 2 * ∑ x : G.Ω 1, ∑ i, ‖σ (x, i) - D.h x i‖ ^ 2 :=
    mul_nonneg (by positivity)
      (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => by positivity)
  linarith

theorem isRealUnitField_constUnitPhi {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) :
    IsRealUnitField G (constUnitPhi G e) := by
  intro x
  refine ⟨fun i => by simp [constUnitPhi], ?_⟩
  simpa [constUnitPhi, Complex.norm_real, sq_abs] using he

theorem constUnitBg_isReal (e : Fin N → ℝ) : (constUnitBg G e).IsReal := by
  intro x i
  by_cases hx : x ∈ dataSites G
  · by_cases hx' : x ∈ G.Ω 1
    · simp [constUnitBg, BgData.clip, hx, hx']
    · simp [constUnitBg, BgData.clip, hx, hx']
  · have : x ∉ G.Ω 1 := fun h => hx ((mem_dataSites G).2 (Or.inl h))
    simp [constUnitBg, BgData.clip, hx, this]

/-- **The constant field is the minimizer of the constant datum**, for every generating set. -/
theorem isMinimizer_constUnitBg {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) {a : ℕ → ℝ}
    (ha : ∀ n, 1 ≤ n → n ≤ K → 0 ≤ a n) {ν : ℝ} (hν : 0 ≤ ν) :
    IsMinimizer G a ν (constUnitBg G e) (constUnitPhi G e) := by
  refine ⟨constUnitBg_isReal e, isRealUnitField_constUnitPhi he, fun σ _ => ?_⟩
  rw [action_constUnitBg_eq_zero]
  exact action_nonneg_layers ha hν _ _


/-- **The constant unit datum lies in `Ψ̃`** for every generating set, mass and radius `r > 0`:
(R1) the differences vanish, (R2) and (R4) `∑ eᵢ² = 1`, (R3) `(e/|e|)·e = 1`. -/
theorem constUnitBg_inPsiTilde {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) (ν : ℝ) {r : ℝ}
    (hr : 0 < r) : InPsiTilde G ν r (fun _ : Torus d (N₀ * L ^ K) => e) e := by
  have hrn : rn e = 1 := by simp [rn, he]
  have he' : ∑ i, e i * e i = 1 := by simpa [sq] using he
  have hr2 : 0 < r ^ 2 := by positivity
  refine ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ => ?_, fun _ _ => ?_, fun _ _ => ?_, ?_⟩
  · simpa [rn] using hr
  · simpa [he] using hr
  · simpa [hrn, he'] using hr2
  · simpa [he] using hr2

theorem constUnitBg_inDomainR {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) (ν : ℝ) {r : ℝ}
    (hr : 0 < r) : InDomainR G ν r (constUnitBg G e) :=
  ⟨fun _ => e, e, constUnitBg_inPsiTilde he ν hr, fun _ hx i => constUnitBg_Ψ hx i,
    fun _ hx i => constUnitBg_h hx i⟩


end Const

section Rows

variable {G : GeneratingSet d L N₀ K ϱ}

theorem layerProj_row_sum {j : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ K) {x : Torus d (N₀ * L ^ K)}
    (hx : x ∈ G.layer j) : ∑ y ∈ G.Ω 1, layerProjMatrix G j x y = 1 := by
  classical
  have hsub : ∀ y ∈ (Finset.univ : Finset (Torus d (N₀ * L ^ K))), y ∉ G.Ω 1 →
      layerProjMatrix G j x y = 0 := by
    intro y _ hy
    have : y ∉ G.layer j := fun h => hy (G.layer_subset hj1 hjK h)
    simp [layerProjMatrix, this]
  rw [Finset.sum_subset (Finset.subset_univ _) (fun y hy hy' => hsub y hy hy')]
  have e : ∀ y, layerProjMatrix G j x y =
      if y ∈ G.blk j x then (((L : ℝ) ^ j) ^ d)⁻¹ else 0 := by
    intro y
    by_cases hy : y ∈ G.blk j x
    · have hb : jBlock d L N₀ K j y = jBlock d L N₀ K j x := GeneratingSet.mem_blk.1 hy
      have hyl : y ∈ G.layer j := (G.mem_layer_iff hj1 hjK hb.symm).1 hx
      have hb' : blockMap (L ^ j) (N₀ * L ^ (K - j)) x = blockMap (L ^ j) (N₀ * L ^ (K - j)) y :=
        hb.symm
      simp only [layerProjMatrix, blockProjMatrix, hx, hyl, hy, hb', and_self, ↓reduceIte]
      push_cast
      rfl
    · simp only [hy, ↓reduceIte, layerProjMatrix, blockProjMatrix]
      by_cases hyl : y ∈ G.layer j
      · have : ¬ blockMap (L ^ j) (N₀ * L ^ (K - j)) x = blockMap (L ^ j) (N₀ * L ^ (K - j)) y :=
          fun hb => hy (GeneratingSet.mem_blk.2 hb.symm)
        simp [hx, hyl, this]
      · simp [hyl]
  rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul, card_blk_cast G j hjK x]
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  field_simp

theorem avgMatrix_row_sum (a : ℕ → ℝ) {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1) :
    ∑ y ∈ G.Ω 1, avgMatrix G a x y =
      a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := G.layerIndex_spec hx
  simp_rw [avgMatrix_apply]
  rw [Finset.sum_comm, Finset.sum_eq_single (G.layerIndex x)]
  · rw [← Finset.mul_sum, layerProj_row_sum h1 h2 h3, mul_one]
  · intro j hj hne
    obtain ⟨hj1, hjK⟩ := Finset.mem_Icc.1 hj
    have : x ∉ G.layer j := G.layer_disjoint h1 h2 hj1 hjK (Ne.symm hne) h3
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [layerProjMatrix, this]
  · intro h
    exact absurd (Finset.mem_Icc.2 ⟨h1, h2⟩) h

theorem latticeLaplacian_row_sum (ν : ℝ) {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1) :
    ∑ y ∈ G.Ω 1, latticeLaplacian d (N₀ * L ^ K) ν x y =
      ν + ∑ μ : Fin d, ((if x + Pi.single μ 1 ∈ G.Ω 1 then (0 : ℝ) else 1) +
        (if x - Pi.single μ 1 ∈ G.Ω 1 then (0 : ℝ) else 1)) := by
  classical
  have h := latticeLaplacian_mulVec ν (fun y => if y ∈ G.Ω 1 then (1 : ℝ) else 0) x
  have hl : (latticeLaplacian d (N₀ * L ^ K) ν).mulVec (fun y => if y ∈ G.Ω 1 then (1 : ℝ) else 0) x =
      ∑ y ∈ G.Ω 1, latticeLaplacian d (N₀ * L ^ K) ν x y := by
    simp [Matrix.mulVec, dotProduct, Finset.sum_ite_mem]
  rw [← hl, h]
  simp only [hx, ↓reduceIte, mul_one]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  split_ifs <;> norm_num

end Rows

section EL

variable {G : GeneratingSet d L N₀ K ϱ}

theorem liftOp_dirichlet_const (e : Fin N → ℝ) (a : ℕ → ℝ) (ν : ℝ) (x : G.Ω 1) (i : Fin N) :
    (liftOp N (dirichletOperator G a ν 0) *ᵥ constUnitPhi G e) (x, i) =
      ((∑ y ∈ G.Ω 1, (latticeLaplacian d (N₀ * L ^ K) ν x.1 y +
        avgMatrix G a x.1 y) : ℝ) : ℂ) * (e i : ℂ) := by
  classical
  simp only [Matrix.mulVec, dotProduct, liftOp, Fintype.sum_prod_type, constUnitPhi]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_coe_sort (G.Ω 1), Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [dirichletOperator_apply]
  simp

theorem collar_term_const (e : Fin N → ℝ) {x y : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1)
    (hadj : Adj x y) (i : Fin N) :
    (if y ∈ collar G then (constUnitBg G e).Ψ y i else 0) =
      ((if y ∈ G.Ω 1 then (0 : ℝ) else 1 : ℝ) : ℂ) * (e i : ℂ) := by
  by_cases hy : y ∈ G.Ω 1
  · have : y ∉ collar G := fun h => ((mem_collar G).1 h).1 hy
    simp [this, hy]
  · have hc : y ∈ collar G := mem_collar_of_adj G hx hy hadj
    simp [hc, hy, constUnitBg_Ψ ((mem_dataSites G).2 (Or.inr hc))]

/-- **The constant field solves the Euler-Lagrange equation with multiplier `0`**:
`H_D(0) φ = S(Ψ, h)` for the constant datum `Ψ ≡ h ≡ e` and `φ ≡ e`: the collar neighbours
contribute `e` to the source exactly where the Dirichlet Laplacian has a missing neighbour. -/
theorem dirichlet_const_eq_source (e : Fin N → ℝ) (a : ℕ → ℝ) (ν : ℝ) (x : G.Ω 1) (i : Fin N) :
    (liftOp N (dirichletOperator G a ν 0) *ᵥ constUnitPhi G e) (x, i) =
      source G a ν (constUnitBg G e) (x, i) := by
  have hb : boundaryTerm G (constUnitBg G e).Ψ (x, i) =
      ((∑ μ : Fin d, ((if x.1 + Pi.single μ 1 ∈ G.Ω 1 then (0 : ℝ) else 1) +
        (if x.1 - Pi.single μ 1 ∈ G.Ω 1 then (0 : ℝ) else 1)) : ℝ) : ℂ) * (e i : ℂ) := by
    unfold boundaryTerm
    rw [Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [collar_term_const e x.2 ⟨μ, Or.inl rfl⟩ i,
      collar_term_const e x.2 ⟨μ, Or.inr (sub_add_cancel _ _).symm⟩ i]
    push_cast
    ring
  rw [liftOp_dirichlet_const, Finset.sum_add_distrib, latticeLaplacian_row_sum ν x.2,
    avgMatrix_row_sum a x.2]
  unfold source qStar
  rw [hb, constUnitBg_Ψ ((mem_dataSites G).2 (Or.inl x.2)), constUnitBg_h x.2]
  push_cast
  ring

end EL

section Background

variable {G : GeneratingSet d L N₀ K ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem bgHyp_weights_nonneg (H : BgHyp d L K ϱ a ν) : ∀ n, 1 ≤ n → n ≤ K → 0 ≤ a n :=
  fun n h1 h2 => by
    have := (H.weights n h1 h2).1
    linarith

/-- **The constant datum is in the real domain `𝒟_ℝ`** under `BgHyp` (only `3 ≤ d` is used, for
the positivity of `c₁`). -/
theorem constUnitBg_inUnionDomainR (H : BgHyp d L K ϱ a ν) {e : Fin N → ℝ}
    (he : ∑ i, e i ^ 2 = 1) : InUnionDomainR G (bgC1 d L N) ν (constUnitBg G e) := by
  have hc : 0 < bgC1 d L N := bgC1_pos_of (by have := H.hd; omega)
  exact ⟨bgC1 d L N, hc, le_rfl, constUnitBg_inDomainR he ν hc⟩

/-- **Uniqueness**: the background field (the unique minimizer) of the constant unit datum is the
constant field. -/
theorem bgField_constUnitBg (H : BgHyp d L K ϱ a ν) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) :
    bgField G a ν (constUnitBg G e) = constUnitPhi G e := by
  have hmin : IsMinimizer G a ν (constUnitBg G e) (constUnitPhi G e) :=
    isMinimizer_constUnitBg he (bgHyp_weights_nonneg H) H.mass
  exact bgField_eq hmin fun φ' hφ' =>
    ((theorem71 H (constUnitBg_inUnionDomainR H he)).1.unique hφ' hmin)

/-- The multiplier of the constant datum is `0`. -/
theorem bgMult_constUnitBg (H : BgHyp d L K ϱ a ν) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) :
    bgMult G a ν (constUnitBg G e) = 0 := by
  funext x
  unfold bgMult
  rw [bgField_constUnitBg H he]
  simp [Pi.sub_apply, dirichlet_const_eq_source]

/-- The complex small solution of the constant datum is the constant field. -/
theorem bgFieldC_constUnitBg (H : BgHyp d L K ϱ a ν) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) :
    bgFieldC G a ν (bgC0 d L N) (constUnitBg G e) = constUnitPhi G e := by
  rw [(theorem72_real H (constUnitBg_inUnionDomainR H he)).1, bgField_constUnitBg H he]

/-- The complex multiplier of the constant datum is `0`. -/
theorem bgMultC_constUnitBg (H : BgHyp d L K ϱ a ν) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) :
    bgMultC G a ν (bgC0 d L N) (constUnitBg G e) = 0 := by
  rw [(theorem72_real H (constUnitBg_inUnionDomainR H he)).2, bgMult_constUnitBg H he]

end Background

/-! ### `Reg` and `χ_k` at the constant field -/

section Cube

variable {M1 N₁ q c n : ℕ} [NeZero M1] [NeZero N₁] [NeZero n]

/-- The cube datum of a constant block field `ψ_q ≡ e` with external field `h = e` is the
constant datum. -/
theorem cubeData_const (e : Fin N → ℝ) (y0 : Torus d n) :
    cubeData (M1 := M1) (N₁ := N₁) (L := L) (q := q) e c n y0 (fun _ i => e i) =
      constUnitBg (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) e := rfl

/-- **`Reg` at the constant field** (cube generating set `G_q(□)`, constant unit block field
`ψ_q ≡ e`, `h = e`): the domain conjunct holds, and `BlockClose`, `GradClose`, `FieldClose` hold for
every tolerance `δ > 0`, because `Ψ = Qφ`, the extension `φ̄` is constant, `α = 0` and `φ = h`. -/
theorem reg_cubeData_const {a : ℕ → ℝ} {μ δ : ℝ}
    (H : BgHyp d L q (minSep L M1) a μ) (hq : 1 ≤ q) (hm : N₁ * L ^ (q - q) = c * n)
    (hδ : 0 < δ) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) (y0 : Torus d n) :
    Reg (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0) a μ
      (cubeData (M1 := M1) (N₁ := N₁) (L := L) (q := q) e c n y0 (fun _ i => e i)) δ
      (cubeNbhd M1 N₁ L q c n 1 y0) (cubeNbhd M1 N₁ L q c n 1 y0) := by
  set G := genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0 with hG
  have hsub : ∀ x ∈ cubeNbhd M1 N₁ L q c n 1 y0, x ∈ G.Ω 1 := fun x hx =>
    G.Ω_antitone le_rfl hq (by omega) (cubeNbhd_one_subset hm y0 x hx)
  rw [cubeData_const]
  have he' : ∑ i, e i * e i = 1 := by simpa [sq] using he
  have hφ := bgFieldC_constUnitBg (G := G) H he
  have hα := bgMultC_constUnitBg (G := G) H he
  refine ⟨constUnitBg_inUnionDomainR H he, ?_, ?_, ?_⟩
  · rw [hφ]
    intro x hx
    have hxΩ := hsub x hx
    unfold blockDev
    have : (fun i => (constUnitBg G e).Ψ x i - blockAvg G (constUnitPhi G e) x i) = 0 := by
      funext i
      rw [blockAvg_constUnitPhi e hxΩ, constUnitBg_Ψ ((mem_dataSites G).2 (Or.inl hxΩ)),
        sub_self]
      rfl
    rw [this, vn_zero]
    exact hδ
  · rw [hφ, hα]
    intro x hx
    have hxΩ := x.2
    have hbar : ∀ y ∈ dataSites G, barVec G (constUnitBg G e) (constUnitPhi G e) y =
        fun i => (e i : ℂ) := fun y hy => funext fun i => barField_constUnitPhi e hy i
    have h0 : ∀ y ∈ dataSites G, barVec G (constUnitBg G e) (constUnitPhi G e) y -
        barVec G (constUnitBg G e) (constUnitPhi G e) x = 0 := by
      intro y hy
      rw [hbar y hy, hbar x ((mem_dataSites G).2 (Or.inl hxΩ)), sub_self]
    have hpos : 0 < ((L : ℝ) ^ q) := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    refine ⟨fun μ' => ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [h0 _ (mem_dataSites_add hxΩ μ'), vn_zero]; simpa using hδ
    · rw [h0 _ (mem_dataSites_sub hxΩ μ'), vn_zero]; simpa using hδ
    · have : barLap G (constUnitBg G e) (constUnitPhi G e) x = 0 := by
        unfold barLap
        refine Finset.sum_eq_zero fun μ' _ => ?_
        rw [hbar _ (mem_dataSites_add hxΩ μ'), hbar _ (mem_dataSites_sub hxΩ μ'),
          hbar x ((mem_dataSites G).2 (Or.inl hxΩ)), two_nsmul]
        abel
      rw [this, vn_zero]; simpa using hδ
    · simpa using hδ
  · rw [hφ]
    intro hν x hx
    have hxΩ := x.2
    have hz : (fun i => constUnitPhi G e (x, i) - (constUnitBg G e).h x i) = 0 := by
      funext i
      rw [constUnitBg_h hxΩ]
      simp [constUnitPhi]
    refine ⟨?_, ?_⟩
    · rw [hz, vn_zero]
      positivity
    · have : ∑ i, (constUnitBg G e).h x i * (constUnitBg G e).h x i - 1 = 0 := by
        have h1 : ∀ i, (constUnitBg G e).h x i = (e i : ℂ) := fun i => constUnitBg_h hxΩ i
        have : ∑ i, (e i : ℂ) * (e i : ℂ) = 1 := by exact_mod_cast he'
        rw [Finset.sum_congr rfl fun i _ => by rw [h1 i], this, sub_self]
      rw [this, norm_zero]
      positivity

/-- **`χ_q(□) = 1` at the constant field**: for every tolerance `δ > 0`. -/
theorem chiK_const_eq_one {a : ℕ → ℝ} {μ δ : ℝ}
    (H : BgHyp d L q (minSep L M1) a μ) (hq : 1 ≤ q) (hm : N₁ * L ^ (q - q) = c * n)
    (hδ : 0 < δ) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) (y0 : Torus d n) :
    chiK (M1 := M1) (N₁ := N₁) (L := L) (q := q) (N := N) a μ δ e c n y0 (fun _ i => e i) = 1 :=
  charFn_eq_one (reg_cubeData_const H hq hm hδ he y0)

end Cube

section Small

open Balaban.LargeField.Def7

variable {S : Setting} {nn : ℕ → ℕ} [∀ k, NeZero (nn k)] {R : ℕ → ℝ} {M KK : ℕ} [NeZero M]
  [NeZero S.L] {k m₁ : ℕ} {ϱ' : ℝ}

/-- **`χ_k(Y) = 1` at the constant unit field**, for every set `Y` of cubes: the small-field
characteristic function of a context with positive tolerance `δ_k` and the cube `BgHyp`
(`3 ≤ d`, `3 ≤ L`, `bgR0 ≤ minSep`, admissible weights, `0 ≤ μ_k`, `μ_k L^{2k} ≤ 1`) at the
constant block field `ψ_k ≡ hv`, `|hv| = 1`. -/
theorem chiY_const_eq_one (C : SFCtx S nn R M KK N k m₁ ϱ') (Y : Set (Torus S.d (nn k)))
    (hv : EuclideanSpace ℝ (Fin N)) (hsum : ∑ i, hv i ^ 2 = 1)
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.mu k)) (hk : 1 ≤ k)
    (hδ : 0 < C.cs.delta k) : C.chiY Y (fun _ => hv) hv = 1 := by
  unfold SFCtx.chiY cubeProd
  refine Finset.prod_eq_one fun y0 _ => ?_
  exact chiK_const_eq_one H hk (by simp) hδ hsum y0

end Small

end Balaban.LargeField
