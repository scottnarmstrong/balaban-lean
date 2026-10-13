/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.KF0WalkTruncation
public import Balaban.LargeField.Base.KF0Gaussian
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# `KF0WalkOrdinary`: the estimate core of Theorem F.1 (path majorant of the walk series)

For the reference square root `C = K_ν^{-1/2}` with walk series `C = ∑_n w_n A^n`
(`kf0C`, `kf0C_hasSum`), the Gaussian field `u = β^{-1/2} C ψ` is, entrywise, the sum over pairs
`(n, y)` of the terms `a_{n,x,y} ψ_y` with `a_{n,x,y} = β^{-1/2} w_n (A^n)_{x y} ≥ 0`.  This file
proves the three estimates that carry the localization of an analytic local function of `u`:

* (T1) the exponentially weighted row sum `∑_n e^{γ n} w_n (2d)^n ≤ A_γ`
  (`kf0_weighted_walk_summable`, `kf0_weighted_row_summable`);
* (T2) the weighted linear substitution on the event `sup_y ‖ψ_y‖ ≤ p`
  (`kf0_substitution_hasSum`, `kf0_substitution_weighted`);
* (T3) the product estimate for monomials: expanding each factor gives a sum over tuples of
  walks, absolutely convergent, with weight `e^{γ · total length}` and total sup-norm at most
  `(p A_γ / √β)^r` (`kf0Term`, `kf0_monomial_*`);
* (T4) the same for a power series with finite absolute majorant (`kf0_series_*`).

This is the estimate core of Theorem F.1 of `notes/phase1/LF-BASE-KF0.md`.  The grouping of the
terms by connected halo, the dependence-set bookkeeping, the block-count inequality (F.10), the
concrete majorants (F.12) of the two local functions, the heavy sector and the one-scale theorem
are NOT proved here.
-/

@[expose] public section

namespace Balaban.Green

open Matrix Finset Filter Topology Balaban.LargeField

/-! ### Products of summable families over a finite power -/

section PiProd

variable {𝕜 : Type} [RCLike 𝕜] {κ : Type}

/-- The statement of `pi_prod_summable_hasSum` for one index type. -/
def PiProdStmt (𝕜 : Type) [RCLike 𝕜] (κ : Type) (ι : Type) [Fintype ι] : Prop :=
  ∀ (f : ι → κ → 𝕜), (∀ i, Summable fun k => ‖f i k‖) →
    Summable (fun τ : ι → κ => ∏ i, ‖f i (τ i)‖) ∧
    HasSum (fun τ : ι → κ => ∏ i, f i (τ i)) (∏ i, ∑' k, f i k)

theorem piProdStmt_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β)
    (ih : PiProdStmt 𝕜 κ α) : PiProdStmt 𝕜 κ β := by
  intro f hf
  obtain ⟨h1, h2⟩ := ih (fun i => f (e i)) (fun i => hf (e i))
  let E : (β → κ) ≃ (α → κ) := Equiv.arrowCongr e.symm (Equiv.refl κ)
  have hE : ∀ τ, E τ = τ ∘ e := fun τ => by
    ext i; simp [E, Equiv.arrowCongr]
  have c1 : (fun τ : β → κ => ∏ i, ‖f i (τ i)‖) =
      (fun σ : α → κ => ∏ i, ‖f (e i) (σ i)‖) ∘ E := by
    ext τ
    simp only [Function.comp, hE]
    exact (Equiv.prod_comp e (fun j => ‖f j (τ j)‖)).symm
  have c2 : (fun τ : β → κ => ∏ i, f i (τ i)) =
      (fun σ : α → κ => ∏ i, f (e i) (σ i)) ∘ E := by
    ext τ
    simp only [Function.comp, hE]
    exact (Equiv.prod_comp e (fun j => f j (τ j))).symm
  refine ⟨?_, ?_⟩
  · rw [c1]; exact E.summable_iff.2 h1
  · rw [c2, E.hasSum_iff, ← Equiv.prod_comp e (fun j => ∑' k, f j k)]; exact h2

theorem piProdStmt_empty : PiProdStmt 𝕜 κ PEmpty := by
  intro f _
  have : Unique (PEmpty → κ) := Pi.uniqueOfIsEmpty _
  refine ⟨?_, ?_⟩
  · simp only [Finset.univ_eq_empty, Finset.prod_empty]; exact Summable.of_finite
  · simp

theorem piProdStmt_option {ι : Type} [Fintype ι] (ih : PiProdStmt 𝕜 κ ι) :
    PiProdStmt 𝕜 κ (Option ι) := by
  intro f hf
  obtain ⟨h1, h2⟩ := ih (fun i => f (some i)) (fun i => hf (some i))
  let E : (Option ι → κ) ≃ κ × (ι → κ) :=
    Equiv.piOptionEquivProd (β := fun _ : Option ι => κ)
  have hE : ∀ τ, E τ = (τ none, fun i => τ (some i)) := fun τ => rfl
  have hn : Summable (fun p : κ × (ι → κ) => ‖f none p.1‖ * ∏ i, ‖f (some i) (p.2 i)‖) :=
    Summable.mul_of_nonneg (hf none) h1 (fun _ => norm_nonneg _)
      (fun _ => Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have c1 : (fun τ : Option ι → κ => ∏ i, ‖f i (τ i)‖) =
      (fun p : κ × (ι → κ) => ‖f none p.1‖ * ∏ i, ‖f (some i) (p.2 i)‖) ∘ E := by
    ext τ
    simp only [Function.comp, hE]
    rw [Fintype.prod_option]
  have c2 : (fun τ : Option ι → κ => ∏ i, f i (τ i)) =
      (fun p : κ × (ι → κ) => f none p.1 * ∏ i, f (some i) (p.2 i)) ∘ E := by
    ext τ
    simp only [Function.comp, hE]
    rw [Fintype.prod_option]
  have hs : Summable (fun p : κ × (ι → κ) => f none p.1 * ∏ i, f (some i) (p.2 i)) := by
    refine Summable.of_norm (hn.congr fun p => ?_)
    simp [norm_mul, norm_prod]
  have hv : (∑' p : κ × (ι → κ), f none p.1 * ∏ i, f (some i) (p.2 i)) =
      (∑' k, f none k) * ∏ i, ∑' k, f (some i) k := by
    rw [← h2.tsum_eq]
    symm
    refine tsum_mul_tsum_of_summable_norm (hf none) ?_
    exact h1.congr fun σ => by simp [norm_prod]
  refine ⟨?_, ?_⟩
  · rw [c1]; exact E.summable_iff.2 hn
  · rw [c2, E.hasSum_iff, Fintype.prod_option]
    rw [← hv]; exact hs.hasSum

/-- Absolutely summable families multiply over `ι → κ`: the sum over all tuples of the product
is the product of the sums, and the family of products of norms is summable. -/
theorem pi_prod_summable_hasSum (ι : Type) [Fintype ι] : PiProdStmt 𝕜 κ ι :=
  Fintype.induction_empty_option (P := fun (ι : Type) _ => PiProdStmt 𝕜 κ ι)
    (fun α β _ e ih => @piProdStmt_equiv 𝕜 _ κ α β (Fintype.ofEquiv β e.symm) _ e ih) piProdStmt_empty
    (fun _ _ ih => piProdStmt_option ih) ι

end PiProd

/-! ### T1: the weighted row sum -/

section Walk

variable {d m : ℕ} [NeZero m]

/-- The constant `A_γ = g^{-1/2} / (1 - q e^γ)`, `q = 2d/(2d+g)`. -/
noncomputable def kf0WalkA (d : ℕ) (g γ : ℝ) : ℝ :=
  (Real.sqrt g)⁻¹ / (1 - 2 * d / (2 * d + g) * Real.exp γ)

/-- The coefficient `a_{n,x,y} = β^{-1/2} w_n (A^n)_{x y}` of `ψ_y` in the `n`-step part of
`u_x = β^{-1/2} (C ψ)_x`. -/
noncomputable def kf0WalkCoeff (d m : ℕ) [NeZero m] (ν β : ℝ) (n : ℕ) (x y : Torus d m) : ℝ :=
  (Real.sqrt β)⁻¹ * (walkWeight d ν n * (kf0Adj d m ^ n) x y)

theorem kf0WalkCoeff_nonneg {ν : ℝ} (hν : 0 < ν) (β : ℝ) (n : ℕ) (x y : Torus d m) :
    0 ≤ kf0WalkCoeff d m ν β n x y :=
  mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
    (mul_nonneg (walkWeight_pos hν n).le (kf0Adj_pow_nonneg n x y))

theorem kf0_weighted_term_le {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) (γ : ℝ) (n : ℕ) :
    Real.exp (γ * n) * (walkWeight d ν n * (2 * d : ℝ) ^ n) ≤
      (Real.sqrt g)⁻¹ * (2 * d / (2 * d + g) * Real.exp γ) ^ n := by
  have h := walkWeight_mul_le_gap (d := d) hg hgν n
  have hexp : Real.exp (γ * n) = Real.exp γ ^ n := by rw [mul_comm, Real.exp_nat_mul]
  rw [hexp]
  calc Real.exp γ ^ n * (walkWeight d ν n * (2 * d : ℝ) ^ n)
      ≤ Real.exp γ ^ n * ((Real.sqrt g)⁻¹ * (2 * d / (2 * d + g)) ^ n) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- **(T1)** `∑_n e^{γ n} w_n (2d)^n ≤ A_γ` for `0 < g ≤ ν` and `q e^γ < 1`. -/
theorem kf0_weighted_walk_summable {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ}
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) :
    Summable (fun n : ℕ => Real.exp (γ * n) * (walkWeight d ν n * (2 * d : ℝ) ^ n)) ∧
      ∑' n : ℕ, Real.exp (γ * n) * (walkWeight d ν n * (2 * d : ℝ) ^ n) ≤ kf0WalkA d g γ := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr0 : 0 ≤ 2 * (d : ℝ) / (2 * d + g) * Real.exp γ := by positivity
  have hs : Summable (fun n : ℕ => (Real.sqrt g)⁻¹ *
      (2 * d / (2 * d + g) * Real.exp γ) ^ n) :=
    (summable_geometric_of_lt_one hr0 hq).mul_left _
  have hnn : ∀ n : ℕ, 0 ≤ Real.exp (γ * n) * (walkWeight d ν n * (2 * d : ℝ) ^ n) :=
    fun n => mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (walkWeight_pos hν n).le (by positivity))
  have hsum := Summable.of_nonneg_of_le hnn (kf0_weighted_term_le (d := d) hg hgν γ) hs
  refine ⟨hsum, ?_⟩
  calc _ ≤ ∑' n : ℕ, (Real.sqrt g)⁻¹ * (2 * d / (2 * d + g) * Real.exp γ) ^ n :=
        hsum.tsum_le_tsum (kf0_weighted_term_le (d := d) hg hgν γ) hs
    _ = kf0WalkA d g γ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hq, kf0WalkA,
          div_eq_mul_inv ((Real.sqrt g)⁻¹)]

/-- **(T1, row form)** for every `x`, `∑_{(n,y)} e^{γ n} w_n (A^n)_{x y} ≤ A_γ`. -/
theorem kf0_weighted_row_summable {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ}
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (x : Torus d m) :
    Summable (fun p : ℕ × Torus d m =>
      Real.exp (γ * p.1) * (walkWeight d ν p.1 * (kf0Adj d m ^ p.1) x p.2)) ∧
      ∑' p : ℕ × Torus d m,
        Real.exp (γ * p.1) * (walkWeight d ν p.1 * (kf0Adj d m ^ p.1) x p.2) ≤
          kf0WalkA d g γ := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  obtain ⟨h1, h2⟩ := kf0_weighted_walk_summable (d := d) hg hgν hq
  have hnn : 0 ≤ (fun p : ℕ × Torus d m =>
      Real.exp (γ * p.1) * (walkWeight d ν p.1 * (kf0Adj d m ^ p.1) x p.2)) :=
    fun p => mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (walkWeight_pos hν _).le (kf0Adj_pow_nonneg _ _ _))
  have hfib : ∀ n : ℕ, ∑' y : Torus d m,
      Real.exp (γ * n) * (walkWeight d ν n * (kf0Adj d m ^ n) x y) =
        Real.exp (γ * n) * (walkWeight d ν n * (2 * d : ℝ) ^ n) := by
    intro n
    rw [tsum_fintype, ← Finset.mul_sum, ← Finset.mul_sum, kf0Adj_pow_rowSum]
  have hS : Summable (fun p : ℕ × Torus d m =>
      Real.exp (γ * p.1) * (walkWeight d ν p.1 * (kf0Adj d m ^ p.1) x p.2)) := by
    refine (summable_prod_of_nonneg hnn).2 ⟨fun n => Summable.of_finite, ?_⟩
    simpa only [hfib] using h1
  refine ⟨hS, ?_⟩
  rw [hS.tsum_prod]
  simp only [hfib]
  exact h2

/-! ### T2: the weighted linear substitution -/

theorem kf0_coeff_weighted_summable {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ}
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (β : ℝ) (x : Torus d m) :
    Summable (fun p : ℕ × Torus d m => Real.exp (γ * p.1) * kf0WalkCoeff d m ν β p.1 x p.2) ∧
      ∑' p : ℕ × Torus d m, Real.exp (γ * p.1) * kf0WalkCoeff d m ν β p.1 x p.2 ≤
        (Real.sqrt β)⁻¹ * kf0WalkA d g γ := by
  obtain ⟨h1, h2⟩ := kf0_weighted_row_summable (d := d) (m := m) hg hgν hq x
  have e : (fun p : ℕ × Torus d m => Real.exp (γ * p.1) * kf0WalkCoeff d m ν β p.1 x p.2) =
      fun p => (Real.sqrt β)⁻¹ *
        (Real.exp (γ * p.1) * (walkWeight d ν p.1 * (kf0Adj d m ^ p.1) x p.2)) := by
    ext p; simp only [kf0WalkCoeff]; ring
  rw [e]
  refine ⟨h1.mul_left _, ?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 (Real.sqrt_nonneg _))

section Subst

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **(T2, identity)** The field `u_x = β^{-1/2} (C ψ)_x` is the sum over `(n, y)` of
`a_{n,x,y} ψ_y`. -/
theorem kf0_substitution_hasSum {ν : ℝ} (hν : 0 < ν) (β : ℝ) (ψ : Torus d m → W)
    (x : Torus d m) :
    HasSum (fun p : ℕ × Torus d m => kf0WalkCoeff d m ν β p.1 x p.2 • ψ p.2)
      ((Real.sqrt β)⁻¹ • matAct (kf0C d m ν) ψ x) := by
  classical
  let G : Torus d m → ℕ × Torus d m → W := fun y p =>
    if p.2 = y then kf0WalkCoeff d m ν β p.1 x y • ψ y else 0
  have hG : ∀ y, HasSum (G y) (((Real.sqrt β)⁻¹ * kf0C d m ν x y) • ψ y) := by
    intro y
    have h0 : HasSum (fun n : ℕ => kf0WalkCoeff d m ν β n x y • ψ y)
        (((Real.sqrt β)⁻¹ * kf0C d m ν x y) • ψ y) := by
      have hh := ((kf0C_hasSum hν x y).mul_left (Real.sqrt β)⁻¹).smul_const (ψ y)
      simpa only [kf0WalkCoeff] using hh
    have hinj : Function.Injective (fun n : ℕ => (n, y)) := fun a b h => by
      simpa using congrArg Prod.fst h
    rw [← hinj.hasSum_iff]
    · simpa [Function.comp_def, G] using h0
    · intro p hp
      have : p.2 ≠ y := fun h => hp ⟨p.1, Prod.ext rfl h.symm⟩
      simp [G, this]
  have hsum := hasSum_sum (s := (Finset.univ : Finset (Torus d m))) (fun y _ => hG y)
  have e1 : (fun b : ℕ × Torus d m => ∑ y, G y b) = fun p : ℕ × Torus d m => kf0WalkCoeff d m ν β p.1 x p.2 • ψ p.2 := by
    ext p : 1
    simp [G]
  have e2 : (∑ y, ((Real.sqrt β)⁻¹ * kf0C d m ν x y) • ψ y) =
      (Real.sqrt β)⁻¹ • matAct (kf0C d m ν) ψ x := by
    simp only [matAct, Finset.smul_sum, mul_smul]
  rw [e1, e2] at hsum
  exact hsum

/-- **(T2, weighted bound)** On the event `sup_y ‖ψ_y‖ ≤ p`,
`∑_{(n,y)} e^{γ n} ‖a_{n,x,y} ψ_y‖ ≤ p A_γ / √β`. -/
theorem kf0_substitution_weighted {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ}
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (β : ℝ) (ψ : Torus d m → W) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : ∀ y, ‖ψ y‖ ≤ p) (x : Torus d m) :
    Summable (fun q : ℕ × Torus d m =>
      Real.exp (γ * q.1) * ‖kf0WalkCoeff d m ν β q.1 x q.2 • ψ q.2‖) ∧
      ∑' q : ℕ × Torus d m, Real.exp (γ * q.1) * ‖kf0WalkCoeff d m ν β q.1 x q.2 • ψ q.2‖ ≤
        p * kf0WalkA d g γ / Real.sqrt β := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  obtain ⟨h1, h2⟩ := kf0_coeff_weighted_summable (d := d) (m := m) (ν := ν) hg hgν hq β x
  have hle : ∀ q : ℕ × Torus d m,
      Real.exp (γ * q.1) * ‖kf0WalkCoeff d m ν β q.1 x q.2 • ψ q.2‖ ≤
        p * (Real.exp (γ * q.1) * kf0WalkCoeff d m ν β q.1 x q.2) := by
    intro q
    rw [norm_smul, Real.norm_of_nonneg (kf0WalkCoeff_nonneg hν β _ _ _)]
    have := mul_le_mul_of_nonneg_left (hp q.2)
      (mul_nonneg (Real.exp_pos (γ * q.1)).le (kf0WalkCoeff_nonneg hν β q.1 x q.2))
    nlinarith [this]
  have hnn : ∀ q : ℕ × Torus d m,
      0 ≤ Real.exp (γ * q.1) * ‖kf0WalkCoeff d m ν β q.1 x q.2 • ψ q.2‖ :=
    fun q => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hs := Summable.of_nonneg_of_le hnn hle (h1.mul_left p)
  refine ⟨hs, ?_⟩
  calc _ ≤ ∑' q : ℕ × Torus d m, p * (Real.exp (γ * q.1) * kf0WalkCoeff d m ν β q.1 x q.2) :=
        hs.tsum_le_tsum hle (h1.mul_left p)
    _ = p * ∑' q : ℕ × Torus d m, Real.exp (γ * q.1) * kf0WalkCoeff d m ν β q.1 x q.2 :=
        tsum_mul_left
    _ ≤ p * ((Real.sqrt β)⁻¹ * kf0WalkA d g γ) := mul_le_mul_of_nonneg_left h2 hp0
    _ = _ := by rw [div_eq_mul_inv]; ring

end Subst

/-! ### T3: monomials -/

section Monomial

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {𝕜 : Type} [RCLike 𝕜]
  {ι : Type} [Fintype ι]

/-- The term of the product expansion of `∏_i ℓ_i(u_{x_i})` indexed by the tuple of walks
`τ i = (n_i, y_i)`: `∏_i a_{n_i,x_i,y_i} ℓ_i(ψ_{y_i})`. -/
noncomputable def kf0Term (d m : ℕ) [NeZero m] (ν β : ℝ) (x : ι → Torus d m)
    (ℓ : ι → W →L[ℝ] 𝕜) (τ : ι → ℕ × Torus d m) (ψ : Torus d m → W) : 𝕜 :=
  ∏ i, ((kf0WalkCoeff d m ν β (τ i).1 (x i) (τ i).2 : ℝ) : 𝕜) * ℓ i (ψ (τ i).2)

/-- The majorant of `e^{γ ∑ n_i} ‖kf0Term‖` on the event `sup_y ‖ψ_y‖ ≤ p`:
`∏_i e^{γ n_i} a_{n_i,x_i,y_i} p`. -/
noncomputable def kf0TermBound (d m : ℕ) [NeZero m] (ν β γ p : ℝ) (x : ι → Torus d m)
    (τ : ι → ℕ × Torus d m) : ℝ :=
  ∏ i, (Real.exp (γ * (τ i).1) * (kf0WalkCoeff d m ν β (τ i).1 (x i) (τ i).2 * p))

/-- Each term depends on `ψ` only through the endpoints `y_i`. -/
theorem kf0Term_congr (d m : ℕ) [NeZero m] (ν β : ℝ) (x : ι → Torus d m)
    (ℓ : ι → W →L[ℝ] 𝕜) (τ : ι → ℕ × Torus d m) {ψ ψ' : Torus d m → W}
    (h : ∀ i, ψ (τ i).2 = ψ' (τ i).2) :
    kf0Term d m ν β x ℓ τ ψ = kf0Term d m ν β x ℓ τ ψ' := by
  unfold kf0Term
  exact Finset.prod_congr rfl fun i _ => by rw [h i]

/-- **(T3, sup bound)** `e^{γ ∑ n_i} sup_{‖ψ‖_∞ ≤ p} |t_τ(ψ)|` is at most `kf0TermBound`. -/
theorem kf0Term_weighted_le {ν : ℝ} (hν : 0 < ν) (β γ p : ℝ) (x : ι → Torus d m)
    (ℓ : ι → W →L[ℝ] 𝕜) (hℓ : ∀ i, ‖ℓ i‖ ≤ 1) (τ : ι → ℕ × Torus d m)
    (ψ : Torus d m → W) (hp : ∀ y, ‖ψ y‖ ≤ p) :
    Real.exp (γ * ∑ i, ((τ i).1 : ℝ)) * ‖kf0Term d m ν β x ℓ τ ψ‖ ≤
      kf0TermBound d m ν β γ p x τ := by
  unfold kf0Term kf0TermBound
  rw [norm_prod, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
  rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (kf0WalkCoeff_nonneg hν β _ _ _)]
  have h1 : ‖ℓ i (ψ (τ i).2)‖ ≤ p :=
    ((ℓ i).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (hℓ i) (norm_nonneg _)).trans
      (by simpa using hp _))
  have h2 := mul_le_mul_of_nonneg_left h1 (kf0WalkCoeff_nonneg hν β (τ i).1 (x i) (τ i).2)
  calc Real.exp (γ * (τ i).1) * (kf0WalkCoeff d m ν β (τ i).1 (x i) (τ i).2 *
        ‖ℓ i (ψ (τ i).2)‖)
      ≤ Real.exp (γ * (τ i).1) * (kf0WalkCoeff d m ν β (τ i).1 (x i) (τ i).2 * p) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := rfl

/-- **(T3, total sup-norm)** The majorant is summable over tuples of walks, with total at most
`(p A_γ / √β)^r`, `r = |ι|`. -/
theorem kf0TermBound_summable {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ}
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (β : ℝ) {p : ℝ} (hp0 : 0 ≤ p)
    (x : ι → Torus d m) :
    Summable (kf0TermBound d m ν β γ p x) ∧
      ∑' τ, kf0TermBound d m ν β γ p x τ ≤
        (p * kf0WalkA d g γ / Real.sqrt β) ^ Fintype.card ι := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  let f : ι → ℕ × Torus d m → ℝ := fun i q =>
    Real.exp (γ * q.1) * (kf0WalkCoeff d m ν β q.1 (x i) q.2 * p)
  have hnn : ∀ i q, 0 ≤ f i q := fun i q =>
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (kf0WalkCoeff_nonneg hν β _ _ _) hp0)
  have hsum : ∀ i, Summable fun q => ‖f i q‖ := by
    intro i
    have := (kf0_coeff_weighted_summable (d := d) (m := m) (ν := ν) hg hgν hq β (x i)).1
    refine (this.mul_right p).congr fun q => ?_
    simp only [f, Real.norm_of_nonneg (hnn i q)]; ring
  obtain ⟨_, h2⟩ := pi_prod_summable_hasSum (𝕜 := ℝ) ι f hsum
  have hB : ∀ i, ∑' q, f i q ≤ p * kf0WalkA d g γ / Real.sqrt β := by
    intro i
    obtain ⟨h1, h3⟩ := kf0_coeff_weighted_summable (d := d) (m := m) (ν := ν) hg hgν hq β (x i)
    have : ∑' q, f i q = p * ∑' q : ℕ × Torus d m, Real.exp (γ * q.1) * kf0WalkCoeff d m ν β q.1 (x i) q.2 := by
      rw [← tsum_mul_left]; exact tsum_congr fun q => by simp only [f]; ring
    rw [this]
    calc _ ≤ p * ((Real.sqrt β)⁻¹ * kf0WalkA d g γ) := mul_le_mul_of_nonneg_left h3 hp0
      _ = _ := by rw [div_eq_mul_inv]; ring
  have e : kf0TermBound d m ν β γ p x = fun τ => ∏ i, f i (τ i) := rfl
  rw [e]
  refine ⟨h2.summable, ?_⟩
  rw [h2.tsum_eq]
  calc ∏ i, ∑' q, f i q ≤ ∏ _i : ι, p * kf0WalkA d g γ / Real.sqrt β :=
        Finset.prod_le_prod₀ (fun i _ => tsum_nonneg (hnn i)) fun i _ => hB i
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

/-- **(T3, identity)** The sum of the terms is the monomial `∏_i ℓ_i(u_{x_i})`,
`u = β^{-1/2} C ψ`, absolutely convergent on the event `sup_y ‖ψ_y‖ ≤ p`. -/
theorem kf0Term_hasSum {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ} (hγ : 0 ≤ γ)
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (β : ℝ) {p : ℝ} (hp0 : 0 ≤ p)
    (x : ι → Torus d m) (ℓ : ι → W →L[ℝ] 𝕜) (hℓ : ∀ i, ‖ℓ i‖ ≤ 1)
    (ψ : Torus d m → W) (hp : ∀ y, ‖ψ y‖ ≤ p) :
    Summable (fun τ : ι → ℕ × Torus d m => ‖kf0Term d m ν β x ℓ τ ψ‖) ∧
      HasSum (fun τ => kf0Term d m ν β x ℓ τ ψ)
        (∏ i, ℓ i ((Real.sqrt β)⁻¹ • matAct (kf0C d m ν) ψ (x i))) := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  let f : ι → ℕ × Torus d m → 𝕜 := fun i q =>
    ((kf0WalkCoeff d m ν β q.1 (x i) q.2 : ℝ) : 𝕜) * ℓ i (ψ q.2)
  have hbd : ∀ i q, ‖f i q‖ ≤ Real.exp (γ * q.1) * (kf0WalkCoeff d m ν β q.1 (x i) q.2 * p) := by
    intro i q
    have h1 : ‖ℓ i (ψ q.2)‖ ≤ p :=
      ((ℓ i).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (hℓ i) (norm_nonneg _)).trans
        (by simpa using hp _))
    have h2 := mul_le_mul_of_nonneg_left h1 (kf0WalkCoeff_nonneg hν β q.1 (x i) q.2)
    have h3 : 1 ≤ Real.exp (γ * q.1) :=
      Real.one_le_exp (mul_nonneg hγ (Nat.cast_nonneg _))
    simp only [f, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (kf0WalkCoeff_nonneg hν β _ _ _)]
    nlinarith [mul_nonneg (kf0WalkCoeff_nonneg hν β q.1 (x i) q.2) hp0]
  have hsum : ∀ i, Summable fun q => ‖f i q‖ := by
    intro i
    have := (kf0_coeff_weighted_summable (d := d) (m := m) (ν := ν) hg hgν hq β (x i)).1
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (hbd i)
      ((this.mul_right p).congr fun q => by ring)
  obtain ⟨h1, h2⟩ := pi_prod_summable_hasSum (𝕜 := 𝕜) ι f hsum
  have hval : ∀ i, ∑' q, f i q =
      ℓ i ((Real.sqrt β)⁻¹ • matAct (kf0C d m ν) ψ (x i)) := by
    intro i
    have h := (ℓ i).hasSum (kf0_substitution_hasSum (d := d) (m := m) hν β ψ (x i))
    have e : f i = fun b : ℕ × Torus d m =>
        ℓ i (kf0WalkCoeff d m ν β b.1 (x i) b.2 • ψ b.2) := by
      ext q
      simp [f, RCLike.real_smul_eq_coe_mul]
    rw [e]
    exact h.tsum_eq
  refine ⟨h1.congr fun τ => by unfold kf0Term; exact (norm_prod _ _).symm, ?_⟩
  rw [Finset.prod_congr rfl fun i _ => hval i] at h2
  exact h2

end Monomial

/-! ### T4: power series -/

section Series

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {𝕜 : Type} [RCLike 𝕜] {D : ℕ}

/-- The factor slots of the monomial with exponent `α`: `α j` slots for the coordinate `j`. -/
abbrev KF0Slot (α : Fin D → ℕ) : Type := Σ j : Fin D, Fin (α j)

/-- The index set of the expanded series: an exponent `α` and a tuple of walks, one for each
factor slot of the monomial `z^α`. -/
abbrev KF0SeriesIndex (d m : ℕ) (D : ℕ) : Type :=
  Σ α : Fin D → ℕ, (KF0Slot α → ℕ × Torus d m)

/-- The term `c_α · ∏_{slots} a ℓ(ψ)` of the expanded series. -/
noncomputable def kf0SeriesTerm (d m : ℕ) [NeZero m] (ν β : ℝ) (x : Fin D → Torus d m)
    (ℓ : Fin D → W →L[ℝ] 𝕜) (c : (Fin D → ℕ) → 𝕜) (ψ : Torus d m → W) :
    KF0SeriesIndex d m D → 𝕜 := fun a =>
  c a.1 * kf0Term d m ν β (fun s : KF0Slot a.1 => x s.1) (fun s => ℓ s.1) a.2 ψ

/-- The majorant `‖c_α‖ θ^{|α|} ∏ ...` of the weighted terms. -/
noncomputable def kf0SeriesBound (d m : ℕ) [NeZero m] (ν β γ p θ : ℝ) (x : Fin D → Torus d m)
    (c : (Fin D → ℕ) → 𝕜) : KF0SeriesIndex d m D → ℝ := fun a =>
  ‖c a.1‖ * θ ^ (∑ j, a.1 j) * kf0TermBound d m ν β γ p (fun s : KF0Slot a.1 => x s.1) a.2

theorem card_kf0Slot (α : Fin D → ℕ) : Fintype.card (KF0Slot α) = ∑ j, α j := by
  simp [Fintype.card_sigma]

/-- **(T4, sup bound)** Termwise: `e^{γ n_tot} θ^{|α|} ‖c_α t‖ ≤ kf0SeriesBound`. -/
theorem kf0SeriesTerm_weighted_le {ν : ℝ} (hν : 0 < ν) (β γ p θ : ℝ) (x : Fin D → Torus d m)
    (ℓ : Fin D → W →L[ℝ] 𝕜) (hℓ : ∀ j, ‖ℓ j‖ ≤ 1) (c : (Fin D → ℕ) → 𝕜)
    (hθ : 0 ≤ θ) (ψ : Torus d m → W) (hp : ∀ y, ‖ψ y‖ ≤ p) (a : KF0SeriesIndex d m D) :
    Real.exp (γ * ∑ s, ((a.2 s).1 : ℝ)) * (θ ^ (∑ j, a.1 j) *
      ‖kf0SeriesTerm d m ν β x ℓ c ψ a‖) ≤ kf0SeriesBound d m ν β γ p θ x c a := by
  have h := kf0Term_weighted_le hν β γ p (fun s : KF0Slot a.1 => x s.1) (fun s => ℓ s.1)
    (fun s => hℓ s.1) a.2 ψ hp
  simp only [kf0SeriesTerm, kf0SeriesBound, norm_mul]
  calc _ = (‖c a.1‖ * θ ^ (∑ j, a.1 j)) * (Real.exp (γ * ∑ s, ((a.2 s).1 : ℝ)) *
        ‖kf0Term d m ν β (fun s : KF0Slot a.1 => x s.1) (fun s => ℓ s.1) a.2 ψ‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

theorem kf0SeriesBound_fiber {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ}
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (β : ℝ) {p : ℝ} (hp0 : 0 ≤ p) {θ : ℝ}
    (hθ : 0 ≤ θ) (x : Fin D → Torus d m) (c : (Fin D → ℕ) → 𝕜) (α : Fin D → ℕ) :
    Summable (fun τ : KF0Slot α → ℕ × Torus d m => kf0SeriesBound d m ν β γ p θ x c ⟨α, τ⟩) ∧
      ∑' τ : KF0Slot α → ℕ × Torus d m, kf0SeriesBound d m ν β γ p θ x c ⟨α, τ⟩ ≤
        ‖c α‖ * (θ * (p * kf0WalkA d g γ / Real.sqrt β)) ^ (∑ j, α j) := by
  set r0 : ℝ := p * kf0WalkA d g γ / Real.sqrt β with hr0
  obtain ⟨h1, h2⟩ := kf0TermBound_summable (d := d) (m := m) (ν := ν) hg hgν hq β hp0
    (fun s : KF0Slot α => x s.1)
  rw [card_kf0Slot] at h2
  have h1' := h1.mul_left (‖c α‖ * θ ^ (∑ j, α j))
  refine ⟨h1'.congr fun τ => rfl, ?_⟩
  have : ∑' τ : KF0Slot α → ℕ × Torus d m, kf0SeriesBound d m ν β γ p θ x c ⟨α, τ⟩ =
      (‖c α‖ * θ ^ (∑ j, α j)) * ∑' τ, kf0TermBound d m ν β γ p
        (fun s : KF0Slot α => x s.1) τ := by
    rw [← tsum_mul_left]; rfl
  rw [this, mul_pow]
  calc _ ≤ (‖c α‖ * θ ^ (∑ j, α j)) * r0 ^ (∑ j, α j) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

theorem kf0SeriesBound_summable {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ}
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (β : ℝ) {p : ℝ} (hp0 : 0 ≤ p) {θ : ℝ}
    (hθ : 0 ≤ θ) (x : Fin D → Torus d m) (c : (Fin D → ℕ) → 𝕜)
    (hM : Summable fun α : Fin D → ℕ =>
      ‖c α‖ * (θ * (p * kf0WalkA d g γ / Real.sqrt β)) ^ (∑ j, α j)) :
    Summable (kf0SeriesBound d m ν β γ p θ x c) ∧
      ∑' a, kf0SeriesBound d m ν β γ p θ x c a ≤
        ∑' α : Fin D → ℕ, ‖c α‖ * (θ * (p * kf0WalkA d g γ / Real.sqrt β)) ^ (∑ j, α j) := by
  have hfib := fun α => kf0SeriesBound_fiber (d := d) (m := m) (ν := ν) hg hgν hq β hp0 hθ x c α
  have hnn : ∀ a, 0 ≤ kf0SeriesBound d m ν β γ p θ x c a := fun a =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hθ _))
      (Finset.prod_nonneg fun i _ => mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (kf0WalkCoeff_nonneg (lt_of_lt_of_le hg hgν) β _ _ _) hp0))
  have hfnn : ∀ α, 0 ≤ ∑' τ : KF0Slot α → ℕ × Torus d m,
      kf0SeriesBound d m ν β γ p θ x c ⟨α, τ⟩ := fun α => tsum_nonneg fun τ => hnn _
  have hS : Summable (kf0SeriesBound d m ν β γ p θ x c) :=
    (summable_sigma_of_nonneg hnn).2 ⟨fun α => (hfib α).1,
      Summable.of_nonneg_of_le hfnn (fun α => (hfib α).2) hM⟩
  refine ⟨hS, ?_⟩
  rw [hS.tsum_sigma']
  · exact (Summable.of_nonneg_of_le hfnn (fun α => (hfib α).2) hM).tsum_le_tsum
      (fun α => (hfib α).2) hM
  · exact fun α => (hfib α).1


/-- **(T4, identity)** On the event `sup_y ‖ψ_y‖ ≤ p`, the family `c_α · t_τ(ψ)` is absolutely
summable and its sum is the series `∑_α c_α ∏_j (ℓ_j u_{x_j})^{α_j}` at `u = β^{-1/2} C ψ`. -/
theorem kf0SeriesTerm_hasSum {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ} (hγ : 0 ≤ γ)
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (β : ℝ) {p : ℝ} (hp0 : 0 ≤ p) {θ : ℝ}
    (hθ : 1 ≤ θ) (x : Fin D → Torus d m) (ℓ : Fin D → W →L[ℝ] 𝕜) (hℓ : ∀ j, ‖ℓ j‖ ≤ 1)
    (c : (Fin D → ℕ) → 𝕜)
    (hM : Summable fun α : Fin D → ℕ =>
      ‖c α‖ * (θ * (p * kf0WalkA d g γ / Real.sqrt β)) ^ (∑ j, α j))
    (ψ : Torus d m → W) (hp : ∀ y, ‖ψ y‖ ≤ p) :
    Summable (fun a => ‖kf0SeriesTerm d m ν β x ℓ c ψ a‖) ∧
      HasSum (kf0SeriesTerm d m ν β x ℓ c ψ)
        (∑' α : Fin D → ℕ, c α * ∏ j, (ℓ j ((Real.sqrt β)⁻¹ •
          matAct (kf0C d m ν) ψ (x j))) ^ (α j)) := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  have hθ0 : 0 ≤ θ := by linarith
  obtain ⟨hB, -⟩ := kf0SeriesBound_summable (d := d) (m := m) (ν := ν) hg hgν hq β hp0 hθ0
    x c hM
  have hle : ∀ a, ‖kf0SeriesTerm d m ν β x ℓ c ψ a‖ ≤ kf0SeriesBound d m ν β γ p θ x c a := by
    intro a
    refine le_trans ?_ (kf0SeriesTerm_weighted_le hν β γ p θ x ℓ hℓ c hθ0 ψ hp a)
    have h1 : 1 ≤ Real.exp (γ * ∑ s, ((a.2 s).1 : ℝ)) :=
      Real.one_le_exp (mul_nonneg hγ (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _))
    have h2 : 1 ≤ θ ^ (∑ j, a.1 j) := one_le_pow₀ hθ
    have h3 := norm_nonneg (kf0SeriesTerm d m ν β x ℓ c ψ a)
    have h4 : 1 ≤ Real.exp (γ * ∑ s, ((a.2 s).1 : ℝ)) * θ ^ (∑ j, a.1 j) :=
      one_le_mul_of_one_le_of_one_le h1 h2
    have h5 := mul_le_mul_of_nonneg_right h4 h3
    linarith [mul_assoc (Real.exp (γ * ∑ s, ((a.2 s).1 : ℝ))) (θ ^ (∑ j, a.1 j))
      ‖kf0SeriesTerm d m ν β x ℓ c ψ a‖]
  have hsn : Summable (fun a => ‖kf0SeriesTerm d m ν β x ℓ c ψ a‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hB
  refine ⟨hsn, ?_⟩
  -- fibres
  have hfibv : ∀ α : Fin D → ℕ,
      HasSum (fun τ : KF0Slot α → ℕ × Torus d m => kf0SeriesTerm d m ν β x ℓ c ψ ⟨α, τ⟩)
        (c α * ∏ j, (ℓ j ((Real.sqrt β)⁻¹ • matAct (kf0C d m ν) ψ (x j))) ^ (α j)) := by
    intro α
    obtain ⟨-, h⟩ := kf0Term_hasSum (d := d) (m := m) (ν := ν) hg hgν hγ hq β hp0
      (fun s : KF0Slot α => x s.1) (fun s => ℓ s.1) (fun s => hℓ s.1) ψ hp
    have h' := h.mul_left (c α)
    have e : (∏ s : KF0Slot α, ℓ s.1 ((Real.sqrt β)⁻¹ • matAct (kf0C d m ν) ψ (x s.1))) =
        ∏ j, (ℓ j ((Real.sqrt β)⁻¹ • matAct (kf0C d m ν) ψ (x j))) ^ (α j) := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp
    rw [e] at h'
    exact h'
  have hnorm : ∀ α : Fin D → ℕ, ‖c α * ∏ j, (ℓ j ((Real.sqrt β)⁻¹ •
      matAct (kf0C d m ν) ψ (x j))) ^ (α j)‖ ≤
      ‖c α‖ * (θ * (p * kf0WalkA d g γ / Real.sqrt β)) ^ (∑ j, α j) := by
    intro α
    obtain ⟨hs, hb⟩ := kf0SeriesBound_fiber (d := d) (m := m) (ν := ν) hg hgν hq β hp0 hθ0 x c α
    have := tsum_of_norm_bounded hs.hasSum (fun τ => hle ⟨α, τ⟩)
    rw [(hfibv α).tsum_eq] at this
    exact this.trans hb
  have hgs : Summable (fun α : Fin D → ℕ => c α * ∏ j, (ℓ j ((Real.sqrt β)⁻¹ •
      matAct (kf0C d m ν) ψ (x j))) ^ (α j)) :=
    Summable.of_norm_bounded hM hnorm
  exact hgs.hasSum.sigma_of_hasSum hfibv hsn.of_norm

end Series

/-! ### T6: an explicit instance, `d = 3`, `L = 3` -/

section Instance

/-- `q e^γ < 1` for `d = 3`, `g = 7/72` (`= kf0Gap 3`), `γ = 1/100`: here `q = 432/439`. -/
theorem kf0_instance_hq : 2 * ((3 : ℕ) : ℝ) / (2 * ((3 : ℕ) : ℝ) + 7 / 72) *
    Real.exp (1 / 100) < 1 := by
  have h := Real.exp_bound_div_one_sub_of_interval (x := 1 / 100) (by norm_num) (by norm_num)
  have hq : 2 * ((3 : ℕ) : ℝ) / (2 * ((3 : ℕ) : ℝ) + 7 / 72) = 432 / 439 := by
    push_cast; norm_num
  rw [hq]
  have h2 : Real.exp (1 / 100) ≤ 100 / 99 := by
    refine h.trans (le_of_eq ?_); norm_num
  calc 432 / 439 * Real.exp (1 / 100) ≤ 432 / 439 * (100 / 99) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ < 1 := by norm_num

theorem kf0_instance_gap : kf0Gap 3 = 7 / 72 := by
  unfold kf0Gap; norm_num

/-- The constant `A_γ` of the instance is explicit and finite: `A ≤ 535`. -/
theorem kf0_instance_A_le : kf0WalkA 3 (7 / 72) (1 / 100) ≤ 535 := by
  have hq := kf0_instance_hq
  set r : ℝ := 2 * ((3 : ℕ) : ℝ) / (2 * ((3 : ℕ) : ℝ) + 7 / 72) * Real.exp (1 / 100) with hr
  have hr' : r ≤ 43200 / 43461 := by
    have h := Real.exp_bound_div_one_sub_of_interval (x := 1 / 100) (by norm_num) (by norm_num)
    have e : 2 * ((3 : ℕ) : ℝ) / (2 * ((3 : ℕ) : ℝ) + 7 / 72) = 432 / 439 := by
      push_cast; norm_num
    rw [hr, e]
    calc 432 / 439 * Real.exp (1 / 100) ≤ 432 / 439 * (1 / (1 - 1 / 100)) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 43200 / 43461 := by norm_num
  have hs : (Real.sqrt (7 / 72 : ℝ))⁻¹ ≤ 321 / 100 := by
    have : (100 / 321 : ℝ) ≤ Real.sqrt (7 / 72) := Real.le_sqrt_of_sq_le (by norm_num)
    calc (Real.sqrt (7 / 72 : ℝ))⁻¹ ≤ (100 / 321 : ℝ)⁻¹ := inv_anti₀ (by norm_num) this
      _ = 321 / 100 := by norm_num
  unfold kf0WalkA
  rw [← hr]
  have hpos : 0 < 1 - r := by linarith
  rw [div_le_iff₀ hpos]
  have hs0 : 0 ≤ (Real.sqrt (7 / 72 : ℝ))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  nlinarith

/-- **(T6)** Non-vacuity of T3 with `r = 2`: `d = 3`, `ν = 1`, `g = 7/72`, `γ = 1/100`,
real-valued `ψ`, two sites `x₀, x₁` and `ℓ = id`. -/
theorem kf0_instance_monomial {m : ℕ} [NeZero m] (β : ℝ) {p : ℝ} (hp0 : 0 ≤ p)
    (x : Fin 2 → Torus 3 m) (ψ : Torus 3 m → ℝ) (hp : ∀ y, ‖ψ y‖ ≤ p) :
    Summable (kf0TermBound 3 m 1 β (1 / 100) p x) ∧
      ∑' τ, kf0TermBound 3 m 1 β (1 / 100) p x τ ≤ (p * 535 / Real.sqrt β) ^ 2 ∧
      Summable (fun τ : Fin 2 → ℕ × Torus 3 m =>
        ‖kf0Term 3 m 1 β x (fun _ => ContinuousLinearMap.id ℝ ℝ) τ ψ‖) ∧
      HasSum (fun τ => kf0Term 3 m 1 β x (fun _ => ContinuousLinearMap.id ℝ ℝ) τ ψ)
        (((Real.sqrt β)⁻¹ • matAct (kf0C 3 m 1) ψ (x 0)) *
          ((Real.sqrt β)⁻¹ • matAct (kf0C 3 m 1) ψ (x 1))) := by
  have hg : (0 : ℝ) < 7 / 72 := by norm_num
  have hgν : (7 / 72 : ℝ) ≤ 1 := by norm_num
  have hq := kf0_instance_hq
  obtain ⟨h1, h2⟩ := kf0TermBound_summable (d := 3) (m := m) (ν := 1) hg hgν hq β hp0 x
  obtain ⟨h3, h4⟩ := kf0Term_hasSum (d := 3) (m := m) (ν := 1) hg hgν (γ := 1 / 100)
    (by norm_num) hq β hp0 x (fun _ => ContinuousLinearMap.id ℝ ℝ)
    (fun _ => ContinuousLinearMap.norm_id_le) ψ hp
  refine ⟨h1, ?_, h3, ?_⟩
  · refine h2.trans ?_
    simp only [Fintype.card_fin]
    have hA := kf0_instance_A_le
    have hs0 : 0 ≤ Real.sqrt β := Real.sqrt_nonneg _
    have : p * kf0WalkA 3 (7 / 72) (1 / 100) / Real.sqrt β ≤ p * 535 / Real.sqrt β :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA hp0) hs0
    exact pow_le_pow_left₀ (div_nonneg (mul_nonneg hp0 (by
      unfold kf0WalkA
      have hd : 0 < 1 - 2 * ((3 : ℕ) : ℝ) / (2 * ((3 : ℕ) : ℝ) + 7 / 72) *
          Real.exp (1 / 100) := by linarith
      positivity)) hs0) this 2
  · simpa [Fin.prod_univ_two] using h4

end Instance



end Walk


end Balaban.Green
