/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.KernelAlgebra
public import Balaban.Multiscale.ConstraintSandwich
public import Balaban.Multiscale.AgmonWeight
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Block decay of the basic operators (GREEN.md §4.5a, §4.6)

The weighted `L²` estimates of the constraint sandwich (`constraintM_lower`,
`agmonSource_commK_le`, `green_vec_bounds`) hold for every admissible weight `w = e^{ε r}`; taking
`r` the truncated path distance to a block (`GeneratingSet.truncDist`) they give the block decay
classes `Dec` of `Balaban.Multiscale.KernelAlgebra`:

* `Dec.of_weighted`: from `‖ℓ w T f‖ ≤ A ‖ℓ w f‖` for all weights to `T ∈ Dec 0 (ε - κ)`;
* `green_dec`: `G_D(α) ∈ Dec 1` (scalar), `liftOp G_D(α) ∈ Dec 1` (vector fields);
* `constraintM_inv_dec`: `M⁻¹ ∈ Dec 0`;
* `commK_green_dec`: `K(φ₀) G_D(α) ∈ Dec 0` with constant proportional to the smoothness.
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Weighted

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
variable (G : GeneratingSet d L N₀ k ϱ)

/-- The weighted source norm `‖ℓ w f‖²` on a general index type with site map `s`. -/
noncomputable def Src {ι : Type*} [Fintype ι] (s : ι → G.Ω 1) (ε : ℝ)
    (r : Torus d (N₀ * L ^ k) → ℝ) (f : ι → ℂ) : ℝ :=
  ∑ p, G.spacing (s p : Torus d (N₀ * L ^ k)) ^ 2 *
    Real.exp (ε * r (s p : Torus d (N₀ * L ^ k))) ^ 2 * ‖f p‖ ^ 2

theorem Src_nonneg {ι : Type*} [Fintype ι] (s : ι → G.Ω 1) (ε : ℝ)
    (r : Torus d (N₀ * L ^ k) → ℝ) (f : ι → ℂ) : 0 ≤ Src G s ε r f :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem agmonSource_eq_Src (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (f : G.Ω 1 → ℂ) :
    agmonSource G ε r f = Src G (id : G.Ω 1 → G.Ω 1) ε r f := by
  rw [agmonSource_eq]; rfl

theorem vecSrc_eq_Src {N : ℕ} (ε : ℝ) (r : Torus d (N₀ * L ^ k) → ℝ) (f : G.Ω 1 × Fin N → ℂ) :
    vecSrc G ε r f = Src G (Prod.fst : G.Ω 1 × Fin N → G.Ω 1) ε r f := by
  unfold vecSrc Src
  simp only [agmonSource_eq]
  rw [Fintype.sum_prod_type_right]
  rfl

variable {G}

theorem Src_lower {ι : Type*} [Fintype ι] (s : ι → G.Ω 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (u : ι → ℂ) :
    ((L : ℝ) ^ j) ^ 2 * Real.exp (2 * ε * (r y - 2 * d)) * bn G s j y u ^ 2 ≤ Src G s ε r u := by
  unfold bn
  rw [l2_sq, Finset.mul_sum]
  unfold Src
  refine Finset.sum_le_sum fun p _ => ?_
  simp only [bproj]
  by_cases hp : jBlock d L N₀ k j (s p : Torus d (N₀ * L ^ k)) = jBlock d L N₀ k j y
  · simp only [hp, ↓reduceIte]
    have hpl : (s p : Torus d (N₀ * L ^ k)) ∈ G.layer j := (G.mem_layer_iff hj1 hjk hp).2 hy
    rw [G.spacing_eq hj1 hjk hpl]
    have hb := hr.block j hj1 hjk y (s p) hy hp
    have h1 : Real.exp (2 * ε * (r y - 2 * d)) ≤ Real.exp (ε * r (s p)) ^ 2 := by
      rw [sq, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := (abs_le.1 hb).2
      nlinarith
    have h2 : 0 ≤ ((L : ℝ) ^ j) ^ 2 * ‖u p‖ ^ 2 := by positivity
    calc ((L : ℝ) ^ j) ^ 2 * Real.exp (2 * ε * (r y - 2 * d)) * ‖u p‖ ^ 2
        = Real.exp (2 * ε * (r y - 2 * d)) * (((L : ℝ) ^ j) ^ 2 * ‖u p‖ ^ 2) := by ring
      _ ≤ Real.exp (ε * r (s p)) ^ 2 * (((L : ℝ) ^ j) ^ 2 * ‖u p‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = _ := by ring
  · simp only [hp, ↓reduceIte, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity

theorem Src_upper {ι : Type*} [Fintype ι] (s : ι → G.Ω 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {j' : ℕ} (hj'1 : 1 ≤ j')
    (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)} (hy' : y' ∈ G.layer j') (hry' : r y' = 0)
    (f : ι → ℂ) :
    Src G s ε r (bproj G s j' y' f) ≤ ((L : ℝ) ^ j') ^ 2 * Real.exp (4 * ε * d) * bn G s j' y' f ^ 2 := by
  unfold bn
  rw [l2_sq, Finset.mul_sum]
  unfold Src
  refine Finset.sum_le_sum fun p _ => ?_
  simp only [bproj]
  by_cases hp : jBlock d L N₀ k j' (s p : Torus d (N₀ * L ^ k)) = jBlock d L N₀ k j' y'
  · simp only [hp, ↓reduceIte]
    have hpl : (s p : Torus d (N₀ * L ^ k)) ∈ G.layer j' := (G.mem_layer_iff hj'1 hj'k hp).2 hy'
    rw [G.spacing_eq hj'1 hj'k hpl]
    have hb := hr.block j' hj'1 hj'k y' (s p) hy' hp
    rw [hry'] at hb
    have h1 : Real.exp (ε * r (s p)) ^ 2 ≤ Real.exp (4 * ε * d) := by
      rw [sq, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := (abs_le.1 hb).1
      nlinarith
    have h2 : 0 ≤ ((L : ℝ) ^ j') ^ 2 * ‖f p‖ ^ 2 := by positivity
    calc ((L : ℝ) ^ j') ^ 2 * Real.exp (ε * r (s p)) ^ 2 * ‖f p‖ ^ 2
        = Real.exp (ε * r (s p)) ^ 2 * (((L : ℝ) ^ j') ^ 2 * ‖f p‖ ^ 2) := by ring
      _ ≤ Real.exp (4 * ε * d) * (((L : ℝ) ^ j') ^ 2 * ‖f p‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = _ := by ring
  · simp only [hp, ↓reduceIte, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity

/-- A nonnegative quantity bounded by `K e^{-ε t}` for all `t ≥ 0` vanishes. -/
theorem eq_zero_of_exp_decay {x K ε : ℝ} (hx : 0 ≤ x) (hK : 0 ≤ K) (hε : 0 < ε)
    (h : ∀ t : ℝ, 0 ≤ t → x ≤ K * Real.exp (-(ε * t))) : x = 0 := by
  by_contra hne
  have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  set t := K / (ε * x) with ht
  have ht0 : 0 ≤ t := by positivity
  have h1 := h t ht0
  have h2 : Real.exp (ε * t) ≥ 1 + ε * t := by linarith [Real.add_one_le_exp (ε * t)]
  have h3 : K * Real.exp (-(ε * t)) * (1 + ε * t) ≤ K := by
    have : Real.exp (-(ε * t)) * Real.exp (ε * t) = 1 := by rw [← Real.exp_add]; simp
    calc K * Real.exp (-(ε * t)) * (1 + ε * t) ≤ K * Real.exp (-(ε * t)) * Real.exp (ε * t) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = K := by rw [mul_assoc, this, mul_one]
  have h4 : ε * t = K / x := by rw [ht]; field_simp
  rw [h4] at h3
  have h5 : x * (1 + K / x) = x + K := by field_simp
  have h6 : x * (1 + K / x) ≤ K * Real.exp (-(ε * t)) * (1 + K / x) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  rw [h4] at h6
  rw [h5] at h6
  rw [h4] at h1
  nlinarith

/-- **From weighted bounds to block decay.**  If `Src (T f) ≤ A² Src f` for all weights
`e^{ε dist(·, y')}` (truncated), then `T ∈ Dec 0 (ε - κ) noTail (A e^{4εd} L)`. -/
theorem Dec.of_weighted {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {T : Matrix ι₁ ι₂ ℂ} {A ε κ : ℝ}
    (hϱ : 1 < ϱ) (hκ : Real.log L ≤ κ * (ϱ - 1)) (hA : 0 ≤ A) (hε0 : 0 < ε)
    (hW : ∀ (y' : Torus d (N₀ * L ^ k)) (t : ℝ), 0 ≤ t → ∀ f : ι₂ → ℂ,
      Src G s₁ ε (G.truncDist y' t) (T *ᵥ f) ≤ A ^ 2 * Src G s₂ ε (G.truncDist y' t) f) :
    Dec G s₁ s₂ T 0 (ε - κ) noTail (A * Real.exp (4 * ε * d) * L) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have key := Dec.of_one_sided (G := G) (s₁ := s₁) (s₂ := s₂) (T := T) (w := 0) (b := 1)
    (A := A * Real.exp (4 * ε * d)) (γ₀ := ε) hϱ hκ (by positivity) (by
      intro j j' y y' hj1 hjk hj'1 hj'k hy hy' f
      set F := bproj G s₂ j' y' f with hF
      have hy'Ω : y' ∈ G.Ω 1 := G.layer_subset hj'1 hj'k hy'
      have hb0 := bn_nonneg s₂ j' y' f
      have hbn0 := bn_nonneg s₁ j y (T *ᵥ F)
      have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
      have hLj' : (0 : ℝ) < (L : ℝ) ^ j' := by positivity
      -- the bound for an admissible truncation parameter
      have hbound : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t ≤ G.pathDist y y' →
          bn G s₁ j y (T *ᵥ F) ≤ A * Real.exp (4 * ε * d) * Real.exp (-(ε * t)) *
            ((L : ℝ) ^ j' / (L : ℝ) ^ j) * bn G s₂ j' y' f := by
        intro t ht0 ht
        have hr := G.isAgmonWeight_truncDist y' t
        have hry : G.truncDist y' t y = t := G.truncDist_eq_of_le ht0 ht
        have hry' : G.truncDist y' t y' = 0 := G.truncDist_self hy'Ω t
        have h1 := Src_lower s₁ hε0.le hr hj1 hjk hy (T *ᵥ F)
        have h2 := hW y' t ht0 F
        have h3 := Src_upper s₂ hε0.le hr hj'1 hj'k hy' hry' f
        rw [hry] at h1
        have h4 : ((L : ℝ) ^ j) ^ 2 * Real.exp (2 * ε * (t - 2 * d)) * bn G s₁ j y (T *ᵥ F) ^ 2 ≤
            A ^ 2 * (((L : ℝ) ^ j') ^ 2 * Real.exp (4 * ε * d) * bn G s₂ j' y' f ^ 2) :=
          h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
        -- take square roots
        have hlhs : (((L : ℝ) ^ j) * Real.exp (ε * (t - 2 * d)) * bn G s₁ j y (T *ᵥ F)) ^ 2 ≤
            (A * ((L : ℝ) ^ j') * Real.exp (2 * ε * d) * bn G s₂ j' y' f) ^ 2 := by
          have e1 : Real.exp (2 * ε * (t - 2 * d)) = Real.exp (ε * (t - 2 * d)) ^ 2 := by
            rw [sq, ← Real.exp_add]; congr 1; ring
          have e2 : Real.exp (4 * ε * d) = Real.exp (2 * ε * d) ^ 2 := by
            rw [sq, ← Real.exp_add]; congr 1; ring
          rw [e1] at h4
          rw [e2] at h4
          nlinarith [h4]
        have h5 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hlhs
        -- rearrange
        have hE : 0 < Real.exp (ε * (t - 2 * d)) := Real.exp_pos _
        have hE2 : Real.exp (2 * ε * d) = Real.exp (ε * (t - 2 * d)) * Real.exp (4 * ε * d) *
            Real.exp (-(ε * t)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        have h6 : bn G s₁ j y (T *ᵥ F) ≤ (A * ((L : ℝ) ^ j') * Real.exp (2 * ε * d) *
            bn G s₂ j' y' f) / (((L : ℝ) ^ j) * Real.exp (ε * (t - 2 * d))) := by
          rw [le_div_iff₀ (by positivity)]; linarith
        refine h6.trans (le_of_eq ?_)
        rw [hE2]
        field_simp
      by_cases hD : G.pathDist y y' = ⊤
      · -- no path: the block norm vanishes
        have hz : bn G s₁ j y (T *ᵥ F) = 0 := by
          refine eq_zero_of_exp_decay (K := A * Real.exp (4 * ε * d) * ((L : ℝ) ^ j' / (L : ℝ) ^ j) *
            bn G s₂ j' y' f) hbn0 (by positivity) hε0 fun t ht0 => ?_
          have := hbound t ht0 (by rw [hD]; exact le_top)
          refine this.trans (le_of_eq ?_)
          ring
        rw [hz, hD, decay_top]
        simp
      · have hne : G.pathDist y y' ≠ ⊤ := hD
        have := hbound (G.pathDist y y').toReal ENNReal.toReal_nonneg
          (by rw [ENNReal.ofReal_toReal hne])
        rw [decay_of_ne_top hne]
        refine this.trans (le_of_eq ?_)
        have e : (((L : ℝ) ^ j) ^ (2 * (0 : ℤ) - 1) * ((L : ℝ) ^ j') ^ (1 : ℤ)) =
            (L : ℝ) ^ j' / (L : ℝ) ^ j := by
          simp [div_eq_mul_inv, mul_comm]
        rw [e]; ring)
  simpa using key

end Weighted

/-! ### Scalar and vector bookkeeping -/

section Vector

variable {N : ℕ} (G : GeneratingSet d L N₀ k ϱ)

theorem bn_id_eq_blockNorm (j : ℕ) (y : Torus d (N₀ * L ^ k)) (u : G.Ω 1 → ℂ) :
    bn G (id : G.Ω 1 → G.Ω 1) j y u = blockNorm G j y u := by
  have h := sqNorm_blockProj G j y u
  have e : bproj G (id : G.Ω 1 → G.Ω 1) j y u = blockProj G j y u := rfl
  unfold bn
  rw [e, l2_eq]
  unfold Green.sqNorm at h
  rw [h, Real.sqrt_sq (blockNorm_nonneg G _ _ _)]

theorem bn_fst_sq (j : ℕ) (y : Torus d (N₀ * L ^ k)) (g : G.Ω 1 × Fin N → ℂ) :
    bn G (Prod.fst : G.Ω 1 × Fin N → G.Ω 1) j y g ^ 2 =
      ∑ i : Fin N, bn G (id : G.Ω 1 → G.Ω 1) j y (comp G g i) ^ 2 := by
  unfold bn
  rw [l2_sq]
  simp only [l2_sq]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [bproj, comp, id]

theorem comp_bproj_fst (j : ℕ) (y : Torus d (N₀ * L ^ k)) (g : G.Ω 1 × Fin N → ℂ) (i : Fin N) :
    comp G (bproj G (Prod.fst : G.Ω 1 × Fin N → G.Ω 1) j y g) i =
      bproj G (id : G.Ω 1 → G.Ω 1) j y (comp G g i) := by
  funext x; simp [comp, bproj]

/-- Componentwise lifting of a scalar block-decay estimate to vector fields. -/
theorem Dec.lift {A : Matrix (G.Ω 1) (G.Ω 1) ℂ} {w : ℤ} {γ C : ℝ}
    {τ : Torus d (N₀ * L ^ k) → Torus d (N₀ * L ^ k) → ℝ} (hC : 0 ≤ C)
    (hτ : ∀ y y', 0 ≤ τ y y') (hA : Dec G (id : G.Ω 1 → G.Ω 1) (id : G.Ω 1 → G.Ω 1) A w γ τ C) :
    Dec G (Prod.fst : G.Ω 1 × Fin N → G.Ω 1) (Prod.fst : G.Ω 1 × Fin N → G.Ω 1) (liftOp N A) w γ τ C := by
  intro j j' y y' hj1 hjk hj'1 hj'k hy hy' f
  set R : ℝ := C * (((L : ℝ) ^ j * (L : ℝ) ^ j') ^ w) * decay γ (G.pathDist y y') * τ y y' with hR
  have hR0 : 0 ≤ R := by
    have := decay_nonneg γ (G.pathDist y y')
    have := hτ y y'
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    rw [hR]; positivity
  have h1 : bn G (Prod.fst : G.Ω 1 × Fin N → G.Ω 1) j y
      (liftOp N A *ᵥ bproj G (Prod.fst : G.Ω 1 × Fin N → G.Ω 1) j' y' f) ^ 2 ≤
      (R * bn G (Prod.fst : G.Ω 1 × Fin N → G.Ω 1) j' y' f) ^ 2 := by
    rw [bn_fst_sq, mul_pow, bn_fst_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [_root_.Balaban.Multiscale.comp_liftOp, comp_bproj_fst, ← mul_pow]
    have := hA j j' y y' hj1 hjk hj'1 hj'k hy hy' (Balaban.Multiscale.comp G f i)
    exact pow_le_pow_left₀ (bn_nonneg _ _ _ _) (by rw [hR]; linarith) 2
  have := (pow_le_pow_iff_left₀ (bn_nonneg _ _ _ _) (mul_nonneg hR0 (bn_nonneg _ _ _ _))
    two_ne_zero).1 h1
  rw [hR] at this
  linarith

end Vector

/-! ### The Green's function -/

section Green

variable (G : GeneratingSet d L N₀ k ϱ) {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ}

/-- **The Green's function is in `Dec 1`** (GREEN.md G-2(i)): with `κ` the scale rate and
`κ ≤ ε₀ / 2`. -/
theorem green_dec (hd : 0 < d) (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) (hϱ : 1 < ϱ) {κ : ℝ}
    (hκ : Real.log L ≤ κ * (ϱ - 1)) (hκ' : κ ≤ agmonRate d / 2) :
    Dec G (id : G.Ω 1 → G.Ω 1) (id : G.Ω 1 → G.Ω 1) (dirichletOperator G a ν α)⁻¹ 1
      (agmonRate d / 2 - κ) noTail (13 * L / poincareConst d * (L : ℝ) ^ ((2 : ℤ) - 1).natAbs) := by
  have hp0 := poincareConst_pos hd
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hr : 0 < ϱ - 1 := by linarith
  have hsep : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) := by
    refine sep_of_log_le (hκ.trans ?_)
    exact mul_le_mul_of_nonneg_right hκ' hr.le
  have key := Dec.of_one_sided (G := G) (s₁ := (id : G.Ω 1 → G.Ω 1)) (s₂ := (id : G.Ω 1 → G.Ω 1))
    (T := (dirichletOperator G a ν α)⁻¹) (w := 1) (b := 2) (A := 13 * L / poincareConst d)
    (γ₀ := agmonRate d / 2) hϱ hκ (by positivity) (by
      intro j j' y y' hj1 hjk hj'1 hj'k hy hy' f
      have h := green_blockNorm_le G hd hν ha α hα hϱ.le hsep hj1 hjk hj'1 hj'k hy hy'
        (f := bproj G (id : G.Ω 1 → G.Ω 1) j' y' f) (by
          intro x hx
          by_contra hne
          exact hx (by simp [bproj, hne]))
      rw [← bn_id_eq_blockNorm] at h
      have e : Real.sqrt (Green.sqNorm (bproj G (id : G.Ω 1 → G.Ω 1) j' y' f)) =
          bn G (id : G.Ω 1 → G.Ω 1) j' y' f := by
        unfold bn; rw [l2_eq]; rfl
      rw [e] at h
      refine h.trans (le_of_eq ?_)
      have : ((L : ℝ) ^ j) ^ (2 * (1 : ℤ) - 2) = 1 := by norm_num
      rw [this]
      have e2 : ((L : ℝ) ^ j') ^ (2 : ℤ) = ((L : ℝ) ^ j') ^ 2 := by norm_cast
      rw [e2]; ring)
  have e3 : ((2 : ℤ) - 1).natAbs = 1 := by norm_num
  simpa [e3] using key

end Green

/-! ### Weighted bounds for the sandwich operators -/

section Sandwich

variable {G : GeneratingSet d L N₀ k ϱ} {N : ℕ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ}

/-- The hypotheses on the Green's function alone. -/
structure GreenData (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) : Prop where
  pos : 0 < d
  mass : 0 ≤ ν
  weights : IsAdmissibleWeights k a
  alpha : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)

theorem Standing.greenData {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (St : Standing G a ν α δ φ) : GreenData G a ν α :=
  ⟨St.pos, St.mass, St.weights, St.alpha⟩

theorem GreenData.vec_bounds (GD : GreenData G a ν α) {r : Torus d (N₀ * L ^ k) → ℝ}
    (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ agmonRate d)
    (g : G.Ω 1 × Fin N → ℂ) :
    vecM G ε r (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) ≤
        4 / poincareConst d ^ 2 * vecSrc G ε r g ∧
      vecGrad G ε r (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) ≤
        10 / poincareConst d * vecSrc G ε r g := by
  have hu : ∀ i, dirichletOperator G a ν α *ᵥ comp G (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) i
      = comp G g i := by
    intro i
    rw [comp_liftOp]
    exact dirichletOperator_mulVec_inv G GD.pos GD.mass GD.weights α GD.alpha _
  refine ⟨?_, ?_⟩
  · rw [vecM_eq, vecSrc, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      agmon_wsq_le G GD.pos GD.mass GD.weights α GD.alpha hr hε0 hε1 (hu i)
  · rw [vecGrad_eq, vecSrc, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      agmon_wgrad_le G GD.pos GD.mass GD.weights α GD.alpha hr hε0 hε1 (hu i)

/-- **Weighted bound for `K(φ₀) Ĝ`** (GREEN.md §4.5a): for a smooth field `φ` (smoothness `δ`),
`‖ℓ w K(φ) Ĝ g‖² ≤ 105 d² δ² (10/c + 4/c²) ‖ℓ w g‖²`. -/
theorem GreenData.commK_green_src (GD : GreenData G a ν α) {δ : ℝ}
    {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ)
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) (g : G.Ω 1 × Fin N → ℂ) :
    agmonSource G ε r (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ
        (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g)) ≤
      105 * d ^ 2 * δ ^ 2 * (10 / poincareConst d + 4 / poincareConst d ^ 2) * vecSrc G ε r g := by
  have hK := agmonSource_commK_le G GD.pos GD.weights ν α hφ hδ hr hε0 hε1
    (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g)
  obtain ⟨hM, hGr⟩ := GD.vec_bounds hr hε0 hε1 g
  have hCg := poincareConst_inv_nonneg GD.pos
  have hV0 := vecSrc_nonneg G ε r g
  have hsum := add_le_add hGr hM
  have hsum' : vecGrad G ε r (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) +
      vecM G ε r (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) ≤
      (10 / poincareConst d + 4 / poincareConst d ^ 2) * vecSrc G ε r g := by
    refine hsum.trans (le_of_eq ?_); ring
  refine hK.trans ?_
  have h0 : (0 : ℝ) ≤ 105 * d ^ 2 * δ ^ 2 := by positivity
  calc 105 * d ^ 2 * δ ^ 2 * (vecGrad G ε r (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) +
      vecM G ε r (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g))
      ≤ 105 * d ^ 2 * δ ^ 2 * ((10 / poincareConst d + 4 / poincareConst d ^ 2) *
        vecSrc G ε r g) := mul_le_mul_of_nonneg_left hsum' h0
    _ = _ := by ring

/-- The constant `√(105 (10/c + 4/c²)) · d` of the commutator estimate. -/
noncomputable def commDecConst (d : ℕ) : ℝ :=
  d * Real.sqrt (105 * (10 / poincareConst d + 4 / poincareConst d ^ 2))

theorem commDecConst_nonneg (d : ℕ) : 0 ≤ commDecConst d := by
  unfold commDecConst; positivity

theorem commDecConst_sq (hd : 0 < d) (δ : ℝ) :
    (commDecConst d * δ) ^ 2 =
      105 * d ^ 2 * δ ^ 2 * (10 / poincareConst d + 4 / poincareConst d ^ 2) := by
  unfold commDecConst
  rw [mul_pow, mul_pow, Real.sq_sqrt (by have := poincareConst_inv_nonneg hd; positivity)]
  ring

/-- **`K(φ₀) Ĝ ∈ Dec 0`** (smallness `δ` of the field). -/
theorem GreenData.commK_green_dec (GD : GreenData G a ν α) {δ : ℝ}
    {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ)
    (hϱ : 1 < ϱ) {κ : ℝ} (hκ : Real.log L ≤ κ * (ϱ - 1)) :
    Dec G (id : G.Ω 1 → G.Ω 1) (Prod.fst : G.Ω 1 × Fin N → G.Ω 1)
      (commK (dirichletOperator G a ν α) (restrictField G φ) *
        liftOp N (dirichletOperator G a ν α)⁻¹) 0 (agmonRate d - κ) noTail
      (commDecConst d * δ * Real.exp (4 * agmonRate d * d) * L) := by
  refine Dec.of_weighted hϱ hκ (mul_nonneg (commDecConst_nonneg d) hδ) (agmonRate_pos GD.pos) ?_
  intro y' t ht f
  have hr := G.isAgmonWeight_truncDist y' t
  rw [← Matrix.mulVec_mulVec, ← agmonSource_eq_Src, ← vecSrc_eq_Src, commDecConst_sq GD.pos]
  exact GD.commK_green_src hφ hδ hr (agmonRate_pos GD.pos).le le_rfl f

/-- **`M⁻¹ ∈ Dec 0`** (the Neumann series of GREEN.md §4.6, in weighted form). -/
theorem constraintM_inv_dec {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (St : Standing G a ν α δ φ) (hϱ : 1 < ϱ) {κ : ℝ} (hκ : Real.log L ≤ κ * (ϱ - 1)) :
    Dec G (id : G.Ω 1 → G.Ω 1) (id : G.Ω 1 → G.Ω 1)
      (constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
        (restrictField G φ))⁻¹ 0 (agmonRate d - κ) noTail
      (2 * Real.exp (4 * agmonRate d * d) * L) := by
  refine Dec.of_weighted hϱ hκ (by norm_num) (agmonRate_pos St.pos) ?_
  intro y' t ht f
  have hr := G.isAgmonWeight_truncDist y' t
  have hU := constraintM_isUnit St
  have hMinv : constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
      (restrictField G φ) * (constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
      (restrictField G φ))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU)
  have h := constraintM_lower St hr (agmonRate_pos St.pos).le le_rfl
    ((constraintM (dirichletOperator G a ν α) (dirichletOperator G a ν α)⁻¹
      (restrictField G φ))⁻¹ *ᵥ f)
  rw [Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec] at h
  rw [← agmonSource_eq_Src, ← agmonSource_eq_Src]
  nlinarith [h]

end Sandwich

end Balaban.Multiscale
