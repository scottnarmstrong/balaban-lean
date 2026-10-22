/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.DataPatch
public import Balaban.Background.CompositionEstimates

/-!
# Patching of local splits of a scaled datum; conditions (R3) in the two mass regimes

The datum of the local pair of the step on a region (reading HS-2) is `θ = z ψ_{k+1}` on the top layer
`Ω_{k+1}` and `ψ_k` elsewhere, while the cube tests of the H7 domain of scale `k + 1` read `ψ_{k+1}`
and `ψ_k`.  This file adapts the patching lemma `inDomainC_of_patch` to a datum equal to `f(x)` times
the value of the split of its chart, `f(x) ∈ {1, z}`, and gives condition (R3) of the patched datum in
the two regimes of the background mass.

* `zShift`, `zShift_add`, `vn_zShift_le`, `norm_quad_zShift_le`: the split `z(Ψ + Ψ') = Ψ + Ψ''`,
  `Ψ'' = Ψ' + (z - 1)(Ψ + Ψ')`, and the bounds of its complex part;
* `scaledTol`, `inDomainC_of_patch_scaled`: **the patching of scaled splits** into
  `Ψ̃^c(3δ₁ + 2ε, 3δ₁ + 2ε)`, `δ₁ = δ + η(2 + η)(1 + 2δ) + 2η(1 + ε + 2δ)`, `|z - 1| ≤ η`;
* `InDomainC.mono_diag`: `Ψ̃^c(t, t) ⊆ Ψ̃^c(t', t')` for `t ≤ t'`;
* `abs_sum_mul_le_rn`, `abs_one_sub_align_le`, `r3_of_small_mass`: **(R3) in the small-mass regime**
  (below `k₀` the cutoff mass of the cube tests vanishes): `ν L^{2q} (1 + |h₀|) < δ²` gives (R3) at every
  layer `≤ q`;
* `r3_of_large_mass`: **(R3) in the large-mass regime** (above `k₀`): from (R3) and (C3b) of a cube test of
  mass `μ ≥ ν` at a layer `≥ l` whose datum has the real external field `h₀`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale

/-- The scaled split: `z (Ψ + Ψ') = Ψ + (Ψ' + (z - 1)(Ψ + Ψ'))`. -/
noncomputable def zShift {N : ℕ} (z : ℝ) (Ψ : Fin N → ℝ) (Ψ' : Fin N → ℂ) : Fin N → ℂ :=
  fun i => Ψ' i + ((z : ℂ) - 1) * ((Ψ i : ℂ) + Ψ' i)

theorem zShift_add {N : ℕ} (z : ℝ) (Ψ : Fin N → ℝ) (Ψ' : Fin N → ℂ) (i : Fin N) :
    (Ψ i : ℂ) + zShift z Ψ Ψ' i = (z : ℂ) * ((Ψ i : ℂ) + Ψ' i) := by
  unfold zShift; ring

theorem vn_const_mul {N : ℕ} (a : ℂ) (v : Fin N → ℂ) : vn (fun i => a * v i) = ‖a‖ * vn v := by
  unfold vn
  have : (WithLp.toLp 2 fun i => a * v i : EuclideanSpace ℂ (Fin N)) = a • WithLp.toLp 2 v := rfl
  rw [this, norm_smul]


/-- The value `Ψ + Ψ'` has norm at most `|Ψ| + |Ψ'|`. -/
theorem vn_add_ofReal_le {N : ℕ} (Ψ : Fin N → ℝ) (Ψ' : Fin N → ℂ) :
    vn (fun i => (Ψ i : ℂ) + Ψ' i) ≤ rn Ψ + vn Ψ' := by
  have := vn_add (fun i => (Ψ i : ℂ)) Ψ'
  rw [vn_ofReal] at this
  exact this

/-- **The complex part of the scaled split** is at most `|Ψ'| + |z - 1| (|Ψ| + |Ψ'|)`. -/
theorem vn_zShift_le {N : ℕ} (z : ℝ) (Ψ : Fin N → ℝ) (Ψ' : Fin N → ℂ) :
    vn (zShift z Ψ Ψ') ≤ vn Ψ' + |z - 1| * (rn Ψ + vn Ψ') := by
  have h1 : zShift z Ψ Ψ' = Ψ' + fun i => ((z : ℂ) - 1) * ((Ψ i : ℂ) + Ψ' i) := by
    funext i; simp [zShift]
  rw [h1]
  refine (vn_add _ _).trans ?_
  rw [vn_const_mul]
  have h2 : ‖(z : ℂ) - 1‖ = |z - 1| := by
    rw [show (z : ℂ) - 1 = ((z - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  rw [h2]
  have := vn_add_ofReal_le Ψ Ψ'
  have h3 : 0 ≤ |z - 1| := abs_nonneg _
  nlinarith

/-- **The quadratic condition (C2b) of the scaled split**:
`|Σ(Ψ + Ψ'')² - ΣΨ²| ≤ z² |Σ(Ψ + Ψ')² - ΣΨ²| + |z² - 1| ΣΨ²`. -/
theorem norm_quad_zShift_le {N : ℕ} (z : ℝ) (Ψ : Fin N → ℝ) (Ψ' : Fin N → ℂ) :
    ‖∑ i, ((Ψ i : ℂ) + zShift z Ψ Ψ' i) * ((Ψ i : ℂ) + zShift z Ψ Ψ' i) -
        ∑ i, (Ψ i : ℂ) * (Ψ i : ℂ)‖ ≤
      z ^ 2 * ‖∑ i, ((Ψ i : ℂ) + Ψ' i) * ((Ψ i : ℂ) + Ψ' i) - ∑ i, (Ψ i : ℂ) * (Ψ i : ℂ)‖ +
        |z ^ 2 - 1| * ∑ i, Ψ i ^ 2 := by
  simp only [zShift_add]
  have e : ∑ i, (z : ℂ) * ((Ψ i : ℂ) + Ψ' i) * ((z : ℂ) * ((Ψ i : ℂ) + Ψ' i)) -
      ∑ i, (Ψ i : ℂ) * (Ψ i : ℂ) =
      ((z ^ 2 : ℝ) : ℂ) * (∑ i, ((Ψ i : ℂ) + Ψ' i) * ((Ψ i : ℂ) + Ψ' i) -
        ∑ i, (Ψ i : ℂ) * (Ψ i : ℂ)) + ((z ^ 2 - 1 : ℝ) : ℂ) * ((∑ i, Ψ i ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    simp only [sq]
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z),
    abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (Ψ i))]

end Balaban.Background

namespace Balaban.Background

open Balaban.Multiscale

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {N : ℕ}

theorem rn_le_of_r2 {v : Fin N → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (h : |∑ i, v i ^ 2 - 1| < δ) :
    rn v ≤ 1 + δ := by
  unfold rn
  rw [Real.sqrt_le_left (by linarith)]
  have := (abs_lt.1 h).2
  nlinarith

/-- The scaled tolerance of `inDomainC_of_patch_scaled`. -/
noncomputable def scaledTol (δ ε η : ℝ) : ℝ :=
  δ + η * (2 + η) * (1 + 2 * δ) + 2 * η * (1 + ε + 2 * δ)

/-- **Patching of local splits of a scaled datum**: as `inDomainC_of_patch`, for a datum whose value at
a data site is `f(x)` times the value `Ψ_{c(x)} + Ψ'_{c(x)}` of the split of its chart, with `f(x) ∈ {1, z}`
and `|z - 1| ≤ η` (the block variable `θ = z ψ_{k+1}` of the step on its top layer, the cube tests reading
`ψ_{k+1}`): the complex parts are shifted by `(f - 1)(Ψ + Ψ')` (`zShift`), which enlarges the tolerance to
`δ₁ = scaledTol δ ε η`; the datum lies in `Ψ̃^c(3δ₁ + 2ε, 3δ₁ + 2ε)`.  Condition (R3) is asked at `δ₁`. -/
theorem inDomainC_of_patch_scaled (D : BgData G N) {ν δ ε η z : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hη : 0 ≤ η) (hz : |z - 1| ≤ η) (f : Torus d (N₀ * L ^ k) → ℝ) (hf : ∀ x, f x = 1 ∨ f x = z)
    (h₀ : Fin N → ℝ) (hDh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h₀ i : ℂ))
    (hR4 : ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < scaledTol δ ε η ^ 2)
    {ι : Type*} (c : Torus d (N₀ * L ^ k) → ι) (Ψc : ι → Torus d (N₀ * L ^ k) → Fin N → ℝ)
    (Ψc' : ι → Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hc : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ G.layer n, ∀ x' ∈ G.blk n x, c x' = c x)
    (hlc : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ G.layer n, ∀ x' ∈ G.blk n x,
      Ψc (c x) x' = Ψc (c x) x ∧ Ψc' (c x) x' = Ψc' (c x) x ∧ f x' = f x)
    (hsplit : ∀ x ∈ dataSites G, ∀ i, D.Ψ x i = (f x : ℂ) * ((Ψc (c x) x i : ℂ) + Ψc' (c x) x i))
    (hR2 : ∀ x ∈ dataSites G, |∑ i, Ψc (c x) x i ^ 2 - 1| < δ)
    (hR3 : ∀ x ∈ dataSites G, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
      |1 - (∑ i, Ψc (c x) x i * h₀ i) / rn (Ψc (c x) x)| < scaledTol δ ε η ^ 2)
    (hC2a : ∀ x ∈ dataSites G, vn (Ψc' (c x) x) < ε + δ)
    (hC2b : ∀ x ∈ dataSites G, ‖∑ i, ((Ψc (c x) x i : ℂ) + Ψc' (c x) x i) *
      ((Ψc (c x) x i : ℂ) + Ψc' (c x) x i) - ∑ i, (Ψc (c x) x i : ℂ) * (Ψc (c x) x i : ℂ)‖ < δ)
    (hpair : ∀ x x', IsInterfacePair G x x' →
      rn (fun i => Ψc (c x) x i - Ψc (c x) x' i) < δ ∧ vn (Ψc' (c x) x - Ψc' (c x) x') < δ ∧
      (∀ i, D.Ψ x' i = (f x' : ℂ) * ((Ψc (c x) x' i : ℂ) + Ψc' (c x) x' i)) ∧
      vn (Ψc' (c x) x') < ε + δ ∧ |∑ i, Ψc (c x) x' i ^ 2 - 1| < δ) :
    InDomainC G ν (3 * scaledTol δ ε η + 2 * ε) (3 * scaledTol δ ε η + 2 * ε) D := by
  set δ₁ := scaledTol δ ε η with hδ₁
  set A := 1 + ε + 2 * δ with hA
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hfη : ∀ x, |f x - 1| ≤ η := fun x => by
    rcases hf x with h | h <;> rw [h]
    · simp [hη]
    · exact hz
  have hδle : δ ≤ δ₁ := by
    rw [hδ₁, scaledTol]; nlinarith [mul_nonneg hη hA0, mul_nonneg (mul_nonneg hη (by linarith : (0:ℝ) ≤ 2 + η)) (by linarith : (0:ℝ) ≤ 1 + 2 * δ)]
  have hδ₁pos : 0 < δ₁ := hδ.trans_le hδle
  -- the value bound `|Ψ| + |Ψ'| ≤ A`
  have hval : ∀ (Ψ : Fin N → ℝ) (Ψ' : Fin N → ℂ), |∑ i, Ψ i ^ 2 - 1| < δ → vn Ψ' < ε + δ →
      rn Ψ + vn Ψ' ≤ A := fun Ψ Ψ' h2 h2a => by
    have := rn_le_of_r2 hδ.le h2
    rw [hA]; linarith
  have hshift : ∀ (x : Torus d (N₀ * L ^ k)) (Ψ : Fin N → ℝ) (Ψ' : Fin N → ℂ),
      |∑ i, Ψ i ^ 2 - 1| < δ → vn Ψ' < ε + δ →
      vn (zShift (f x) Ψ Ψ') - vn Ψ' ≤ η * A := fun x Ψ Ψ' h2 h2a => by
    have h1 := vn_zShift_le (f x) Ψ Ψ'
    have h3 := hval Ψ Ψ' h2 h2a
    have h4 := hfη x
    have : |f x - 1| * (rn Ψ + vn Ψ') ≤ η * A :=
      mul_le_mul h4 h3 (add_nonneg (Real.sqrt_nonneg _) (vn_nonneg _)) hη
    linarith
  refine inDomainC_of_patch D hδ₁pos hε h₀ hDh hR4 c Ψc
    (fun j x => zShift (f x) (Ψc j x) (Ψc' j x)) hc ?_ ?_ (fun x hx => (hR2 x hx).trans_le hδle)
    hR3 ?_ ?_ ?_
  · intro n hn1 hnk x hx x' hx'
    obtain ⟨h1, h2, h3⟩ := hlc n hn1 hnk x hx x' hx'
    refine ⟨h1, ?_⟩
    show zShift (f x') (Ψc (c x) x') (Ψc' (c x) x') = zShift (f x) (Ψc (c x) x) (Ψc' (c x) x)
    rw [h1, h2, h3]
  · intro x hx i
    rw [hsplit x hx i, zShift_add]
  · intro x hx
    have := hshift x _ _ (hR2 x hx) (hC2a x hx)
    have hle : η * A ≤ δ₁ - δ := by
      rw [hδ₁, scaledTol, hA]; nlinarith [mul_nonneg (mul_nonneg hη (by linarith : (0:ℝ) ≤ 2 + η)) (by linarith : (0:ℝ) ≤ 1 + 2 * δ), mul_nonneg hη hA0]
    linarith [hC2a x hx]
  · intro x hx
    have h1 := norm_quad_zShift_le (f x) (Ψc (c x) x) (Ψc' (c x) x)
    have hf2 : f x ^ 2 ≤ (1 + η) ^ 2 := by
      have := hfη x
      have h0 : |f x| ≤ 1 + η := by
        have := abs_sub_abs_le_abs_sub (f x) 1
        rw [abs_one] at this; linarith
      calc f x ^ 2 = |f x| ^ 2 := (sq_abs _).symm
        _ ≤ (1 + η) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h0 2
    have hf21 : |f x ^ 2 - 1| ≤ η * (2 + η) := by
      have := hfη x
      have h0 : |f x + 1| ≤ 2 + η := by
        have : f x + 1 = (f x - 1) + 2 := by ring
        rw [this]; refine (abs_add_le _ _).trans ?_; rw [abs_two]; linarith
      rw [show f x ^ 2 - 1 = (f x - 1) * (f x + 1) by ring, abs_mul]
      exact mul_le_mul this h0 (abs_nonneg _) hη
    have hsum : ∑ i, Ψc (c x) x i ^ 2 ≤ 1 + δ := by
      have := (abs_lt.1 (hR2 x hx)).2; linarith
    have hsum0 : 0 ≤ ∑ i, Ψc (c x) x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hq := hC2b x hx
    have hqn := norm_nonneg (∑ i, ((Ψc (c x) x i : ℂ) + Ψc' (c x) x i) *
      ((Ψc (c x) x i : ℂ) + Ψc' (c x) x i) - ∑ i, (Ψc (c x) x i : ℂ) * (Ψc (c x) x i : ℂ))
    refine h1.trans_lt ?_
    have e1 : f x ^ 2 * ‖∑ i, ((Ψc (c x) x i : ℂ) + Ψc' (c x) x i) *
        ((Ψc (c x) x i : ℂ) + Ψc' (c x) x i) - ∑ i, (Ψc (c x) x i : ℂ) * (Ψc (c x) x i : ℂ)‖ <
        (1 + η) ^ 2 * δ := by
      rcases (sq_nonneg (f x)).eq_or_lt with h0 | h0
      · rw [← h0, zero_mul]; positivity
      · calc _ < f x ^ 2 * δ := mul_lt_mul_of_pos_left hq h0
          _ ≤ (1 + η) ^ 2 * δ := mul_le_mul_of_nonneg_right hf2 hδ.le
    have e2 : |f x ^ 2 - 1| * ∑ i, Ψc (c x) x i ^ 2 ≤ η * (2 + η) * (1 + δ) :=
      mul_le_mul hf21 hsum hsum0 (by positivity)
    have : (1 + η) ^ 2 * δ + η * (2 + η) * (1 + δ) ≤ δ₁ := by
      rw [hδ₁, scaledTol]; nlinarith [mul_nonneg hη hA0]
    linarith
  · intro x x' hxx'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpair x x' hxx'
    have hx : x ∈ dataSites G := hxx'.1
    refine ⟨h1.trans_le hδle, ?_, fun i => by rw [h3 i, zShift_add], ?_⟩
    · -- the difference of the shifted complex parts
      have e : zShift (f x) (Ψc (c x) x) (Ψc' (c x) x) - zShift (f x') (Ψc (c x) x') (Ψc' (c x) x') =
          (Ψc' (c x) x - Ψc' (c x) x') +
            ((zShift (f x) (Ψc (c x) x) (Ψc' (c x) x) - Ψc' (c x) x) -
              (zShift (f x') (Ψc (c x) x') (Ψc' (c x) x') - Ψc' (c x) x')) := by abel
      have hb : ∀ (y : Torus d (N₀ * L ^ k)) (Ψ : Fin N → ℝ) (Ψ' : Fin N → ℂ),
          |∑ i, Ψ i ^ 2 - 1| < δ → vn Ψ' < ε + δ → vn (zShift (f y) Ψ Ψ' - Ψ') ≤ η * A :=
        fun y Ψ Ψ' hr2 hc2 => by
          have e' : zShift (f y) Ψ Ψ' - Ψ' = fun i => ((f y : ℂ) - 1) * ((Ψ i : ℂ) + Ψ' i) := by
            funext i; simp [zShift]
          rw [e', vn_const_mul]
          have h2' : ‖(f y : ℂ) - 1‖ = |f y - 1| := by
            rw [show (f y : ℂ) - 1 = ((f y - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
              Real.norm_eq_abs]
          rw [h2']
          exact mul_le_mul (hfη y) ((vn_add_ofReal_le Ψ Ψ').trans (hval Ψ Ψ' hr2 hc2))
            (vn_nonneg _) hη
      have hx1 := hb x _ _ (hR2 x hx) (hC2a x hx)
      have hx2 := hb x' _ _ h5 h4
      rw [e]
      refine (vn_add _ _).trans_lt ?_
      have hsub := vn_sub_le (zShift (f x) (Ψc (c x) x) (Ψc' (c x) x) - Ψc' (c x) x)
        (zShift (f x') (Ψc (c x) x') (Ψc' (c x) x') - Ψc' (c x) x')
      have : δ + 2 * (η * A) ≤ δ₁ := by
        rw [hδ₁, scaledTol, hA]; nlinarith [mul_nonneg (mul_nonneg hη (by linarith : (0:ℝ) ≤ 2 + η)) (by linarith : (0:ℝ) ≤ 1 + 2 * δ)]
      linarith
    · have := hshift x' _ _ h5 h4
      have hle : η * A ≤ δ₁ - δ := by
        rw [hδ₁, scaledTol, hA]; nlinarith [mul_nonneg (mul_nonneg hη (by linarith : (0:ℝ) ≤ 2 + η)) (by linarith : (0:ℝ) ≤ 1 + 2 * δ), mul_nonneg hη hA0]
      linarith

end Balaban.Background

namespace Balaban.Background

open Balaban.Multiscale

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {N : ℕ}

/-- **Monotonicity of the diagonal domains** `Ψ̃^c(t, t) ⊆ Ψ̃^c(t', t')` for `t ≤ t'`. -/
theorem InDomainC.mono_diag {ν t t' : ℝ} {D : BgData G N} (h : InDomainC G ν t t D) (htt : t ≤ t') :
    InDomainC G ν t' t' D := by
  obtain ⟨Ψ, h₀, Ψ', h', hP, hΨ, hh⟩ := h
  have ht : 0 < t := hP.eps_pos
  have ht' : 0 < t' := ht.trans_le htt
  have hsq : t ^ 2 ≤ t' ^ 2 := pow_le_pow_left₀ ht.le htt 2
  refine ⟨Ψ, h₀, Ψ', h', ?_, hΨ, hh⟩
  refine
    { layerConst := hP.layerConst
      r1 := fun x x' hxx' => (hP.r1 x x' hxx').trans_le htt
      r2 := fun x hx => (hP.r2 x hx).trans_le htt
      r3 := fun x hx => (hP.r3 x hx).trans_le hsq
      r4 := hP.r4.trans_le hsq
      eps_pos := ht'
      layerConst' := hP.layerConst'
      hLayerConst' := hP.hLayerConst'
      c1 := fun x x' hxx' => (hP.c1 x x' hxx').trans_le htt
      c2a := fun x hx => (hP.c2a x hx).trans_le (by linarith)
      c2b := fun x hx => (hP.c2b x hx).trans_le htt
      c3a := fun x hx => by
        have := hP.c3a x hx
        rw [show t ^ 2 / t = t by field_simp] at this
        rw [show t' ^ 2 / t' = t' by field_simp]
        exact this.trans_le htt
      c3b := fun x hx => (hP.c3b x hx).trans_le hsq }

end Balaban.Background


namespace Balaban.Background

open Balaban.Multiscale

/-- `|v · w| ≤ |v| |w|` for the norm `rn`. -/
theorem abs_sum_mul_le_rn {N : ℕ} (v w : Fin N → ℝ) : |∑ i, v i * w i| ≤ rn v * rn w := by
  have h := abs_real_inner_le_norm (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))
    (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin N))
  rw [← rn_eq_norm, ← rn_eq_norm] at h
  have e : inner ℝ (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N)) (WithLp.toLp 2 w) = ∑ i, v i * w i := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, mul_comm]
  rw [e] at h
  exact h

/-- The alignment defect of condition (R3) is at most `1 + |h₀|`. -/
theorem abs_one_sub_align_le {N : ℕ} (Ψ h₀ : Fin N → ℝ) :
    |1 - (∑ i, Ψ i * h₀ i) / rn Ψ| ≤ 1 + rn h₀ := by
  have h1 : |(∑ i, Ψ i * h₀ i) / rn Ψ| ≤ rn h₀ := by
    rcases (Real.sqrt_nonneg (∑ i, Ψ i ^ 2)).eq_or_lt with h0 | hpos
    · have : rn Ψ = 0 := by unfold rn; exact h0.symm
      rw [this, div_zero, abs_zero]
      exact Real.sqrt_nonneg _
    · have hpos' : 0 < rn Ψ := hpos
      rw [abs_div, abs_of_pos hpos', div_le_iff₀ hpos']
      have := abs_sum_mul_le_rn Ψ h₀
      linarith [mul_comm (rn Ψ) (rn h₀)]
  calc |1 - (∑ i, Ψ i * h₀ i) / rn Ψ| ≤ |1| + |(∑ i, Ψ i * h₀ i) / rn Ψ| := abs_sub _ _
    _ ≤ 1 + rn h₀ := by rw [abs_one]; linarith

/-- **Condition (R3) in the small-mass regime** (below `k₀`, where the cutoff mass of the cube tests
vanishes): if `ν L^{2q} (1 + |h₀|) < δ²`, condition (R3) holds at every layer `l ≤ q`, for every real
field. -/
theorem r3_of_small_mass {N : ℕ} {ν δ : ℝ} (hν : 0 ≤ ν) {L l q : ℕ} (hL : 1 ≤ L) (hl : l ≤ q)
    (h₀ : Fin N → ℝ) (hsmall : ν * ((L : ℝ) ^ q) ^ 2 * (1 + rn h₀) < δ ^ 2) (Ψ : Fin N → ℝ) :
    ν * ((L : ℝ) ^ l) ^ 2 * |1 - (∑ i, Ψ i * h₀ i) / rn Ψ| < δ ^ 2 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hpow : ((L : ℝ) ^ l) ^ 2 ≤ ((L : ℝ) ^ q) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 hl) 2
  have hA := abs_one_sub_align_le Ψ h₀
  calc ν * ((L : ℝ) ^ l) ^ 2 * |1 - (∑ i, Ψ i * h₀ i) / rn Ψ|
      ≤ ν * ((L : ℝ) ^ q) ^ 2 * (1 + rn h₀) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hpow hν) hA (abs_nonneg _)
        positivity
    _ < δ ^ 2 := hsmall

/-- **Condition (R3) in the large-mass regime** (above `k₀`): from the conditions (R3) and (C3b) of a cube
test with mass `μ ≥ ν` at a layer `l_c ≥ l`, whose real external field is `h` and whose complex
perturbation is the real constant `h' = h₀ - h` (the datum of the test has external field `h₀`):
`ν L^{2l} |1 - Ψ·h₀/|Ψ|| < 2ε²`. -/
theorem r3_of_large_mass {N : ℕ} {ν μ ε : ℝ} (hν : 0 ≤ ν) (hνμ : ν ≤ μ) {L l lc : ℕ} (hL : 1 ≤ L)
    (hl : l ≤ lc) (Ψ h h₀ : Fin N → ℝ) (h' : Fin N → ℂ) (hh' : ∀ i, h' i = ((h₀ i - h i : ℝ) : ℂ))
    (hr3 : μ * ((L : ℝ) ^ lc) ^ 2 * |1 - (∑ i, Ψ i * h i) / rn Ψ| < ε ^ 2)
    (hc3b : μ * ((L : ℝ) ^ lc) ^ 2 * ‖∑ i, ((Ψ i / rn Ψ : ℝ) : ℂ) * h' i‖ < ε ^ 2) :
    ν * ((L : ℝ) ^ l) ^ 2 * |1 - (∑ i, Ψ i * h₀ i) / rn Ψ| < 2 * ε ^ 2 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hpow : ((L : ℝ) ^ l) ^ 2 ≤ ((L : ℝ) ^ lc) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 hl) 2
  have hμ0 : 0 ≤ μ := hν.trans hνμ
  have hsum : ∑ i, ((Ψ i / rn Ψ : ℝ) : ℂ) * h' i = (((∑ i, Ψ i * h₀ i) / rn Ψ -
      (∑ i, Ψ i * h i) / rn Ψ : ℝ) : ℂ) := by
    simp only [hh']
    push_cast
    rw [← sub_div, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum, Complex.norm_real, Real.norm_eq_abs] at hc3b
  have htri : |1 - (∑ i, Ψ i * h₀ i) / rn Ψ| ≤ |1 - (∑ i, Ψ i * h i) / rn Ψ| +
      |(∑ i, Ψ i * h₀ i) / rn Ψ - (∑ i, Ψ i * h i) / rn Ψ| := by
    have : 1 - (∑ i, Ψ i * h₀ i) / rn Ψ = (1 - (∑ i, Ψ i * h i) / rn Ψ) -
        ((∑ i, Ψ i * h₀ i) / rn Ψ - (∑ i, Ψ i * h i) / rn Ψ) := by ring
    rw [this]; exact abs_sub _ _
  have hA : 0 ≤ ν * ((L : ℝ) ^ l) ^ 2 := by positivity
  calc ν * ((L : ℝ) ^ l) ^ 2 * |1 - (∑ i, Ψ i * h₀ i) / rn Ψ|
      ≤ μ * ((L : ℝ) ^ lc) ^ 2 * (|1 - (∑ i, Ψ i * h i) / rn Ψ| +
          |(∑ i, Ψ i * h₀ i) / rn Ψ - (∑ i, Ψ i * h i) / rn Ψ|) :=
        mul_le_mul (mul_le_mul hνμ hpow (by positivity) hμ0) htri (abs_nonneg _) (by positivity)
    _ < 2 * ε ^ 2 := by rw [mul_add]; linarith

end Balaban.Background
