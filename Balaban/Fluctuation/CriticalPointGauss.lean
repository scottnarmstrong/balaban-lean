module

public import Balaban.Background.Theorem73
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Lemma 2.2 (a): the Gaussian composition (FLUCTUATION.md §2.2)

Fine units of Background (`η = 1`, `ℓ_j = L^j`; FLUCTUATION §1.1): with the weights
`a_j = compWeight L a₁ j` of (6.1) (`a₁` is the constant `a` of P4 (2.1)), the coupling of the
block field `θ` to the lifted field `Ψ` is `½ a₁ L^{-2p} ∑_x |θ - Q_p Ψ|²` (`p = k + 1`), the level
term of the action of level `n = k` is `½ a_n L^{-2n} ∑_x |Ψ - Q_n φ|²`.

* `compWeight_harmonic`, `weight_relation`, `compWeight_succ`: `a_{n+1} = a₁ a_n / (a_n + a₁ L⁻²)`;
* `coupling_add_level`: `coupling + level_n = level_{n+1} + defect`, an exact completion of squares
  (`Q_p` is the orthogonal projection onto `p`-block constants, `sum_norm_sq_decomp`);
* `defect_nonneg`, `defect_eq_zero_iff`, `gaussianComposition`: the minimum over `Ψ` is
  `level_{n+1}(θ, φ)`, attained exactly at `Ψ(θ, φ)` of (2.1) (`psiStar`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

section Blocks

variable {G : GeneratingSet d L N₀ K ϱ}

theorem blockMean_mul_const {p : ℕ} (g w : Torus d (N₀ * L ^ K) → ℂ)
    (hg : ∀ x y, y ∈ G.blk p x → g y = g x) (x : Torus d (N₀ * L ^ K)) :
    blockMean G p (fun y => g y * w y) x = g x * blockMean G p w x := by
  unfold blockMean
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [hg x y hy]; ring

theorem blockMean_blk_const {p : ℕ} (w : Torus d (N₀ * L ^ K) → ℂ) (x y : Torus d (N₀ * L ^ K))
    (hy : y ∈ G.blk p x) : blockMean G p w y = blockMean G p w x :=
  blockMean_congr w (blk_eq_of_mem hy)

/-- Orthogonal decomposition of `ℓ²` along the `p`-block averages. -/
theorem sum_norm_sq_decomp {p : ℕ} (hp : p ≤ K) (A : Torus d (N₀ * L ^ K) → ℂ) :
    ∑ x, ‖A x‖ ^ 2 = ∑ x, ‖A x - blockMean G p A x‖ ^ 2 + ∑ x, ‖blockMean G p A x‖ ^ 2 := by
  have hn : ∀ z : Torus d (N₀ * L ^ K), (fun _ => p) z ≤ K := fun _ => hp
  have h1 : ∑ z ∈ (Finset.univ : Finset (Torus d (N₀ * L ^ K))),
      blockMean G ((fun _ => p) z) (fun y => (starRingEnd ℂ) (blockMean G p A y) * A y) z =
      ∑ z ∈ (Finset.univ : Finset (Torus d (N₀ * L ^ K))),
        (fun y => (starRingEnd ℂ) (blockMean G p A y) * A y) z :=
    sum_blockMean_nested G Finset.univ (fun _ => p) hn _ (fun _ _ _ _ =>
      ⟨Finset.mem_univ _, rfl⟩)
  have h2 : ∀ x, blockMean G p (fun y => (starRingEnd ℂ) (blockMean G p A y) * A y) x =
      (starRingEnd ℂ) (blockMean G p A x) * blockMean G p A x := fun x =>
    blockMean_mul_const _ _ (fun x y hy => by rw [blockMean_blk_const A x y hy]) x
  simp only [h2] at h1
  have h3 : ∑ x, (A x - blockMean G p A x) * (starRingEnd ℂ) (blockMean G p A x) = 0 := by
    have : ∀ x, (A x - blockMean G p A x) * (starRingEnd ℂ) (blockMean G p A x) =
        (starRingEnd ℂ) (blockMean G p A x) * A x -
          (starRingEnd ℂ) (blockMean G p A x) * blockMean G p A x := fun x => by ring
    simp only [this, Finset.sum_sub_distrib]
    rw [h1]; ring
  have h4 : ∑ x, ((A x - blockMean G p A x) * (starRingEnd ℂ) (blockMean G p A x)).re = 0 := by
    rw [← Complex.re_sum, h3]; simp
  have h5 : ∀ x, ‖A x‖ ^ 2 = ‖A x - blockMean G p A x‖ ^ 2 + ‖blockMean G p A x‖ ^ 2 +
      2 * ((A x - blockMean G p A x) * (starRingEnd ℂ) (blockMean G p A x)).re := fun x => by
    have := Complex.normSq_add (A x - blockMean G p A x) (blockMean G p A x)
    simp only [sub_add_cancel] at this
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]; exact this
  simp only [h5, Finset.sum_add_distrib, ← Finset.mul_sum, h4]
  ring

/-- The block mean of a function that is constant on the block is the constant. -/
theorem blockMean_of_blk_const {p : ℕ} (hp : p ≤ K) (w : Torus d (N₀ * L ^ K) → ℂ)
    (x : Torus d (N₀ * L ^ K)) (hw : ∀ y ∈ G.blk p x, w y = w x) :
    blockMean G p w x = w x := by
  have : blockMean G p w x = blockMean G p (fun _ => w x) x := by
    unfold blockMean
    exact congrArg _ (Finset.sum_congr rfl hw)
  rw [this, blockMean_const G hp]

/-- Nested block means: `Q_p Q_n = Q_p` for `n ≤ p`. -/
theorem blockMean_nested {n p : ℕ} (hnp : n ≤ p) (hp : p ≤ K) (f : Torus d (N₀ * L ^ K) → ℂ)
    (x : Torus d (N₀ * L ^ K)) :
    blockMean G p (fun y => blockMean G n f y) x = blockMean G p f x := by
  have h := sum_blockMean_nested G (G.blk p x) (fun _ => n) (fun _ => hnp.trans hp) f
    (fun z hz y hy => by
      refine ⟨?_, rfl⟩
      rw [GeneratingSet.mem_blk] at hz ⊢
      exact (jBlock_eq_of_le hnp hp (GeneratingSet.mem_blk.1 hy)).trans hz)
  have e1 : blockMean G p (fun y => blockMean G n f y) x =
      ((((((L : ℝ) ^ p) ^ d)⁻¹ : ℝ) : ℂ)) * ∑ z ∈ G.blk p x, blockMean G n f z := rfl
  have e2 : blockMean G p f x = ((((((L : ℝ) ^ p) ^ d)⁻¹ : ℝ) : ℂ)) * ∑ z ∈ G.blk p x, f z := rfl
  rw [e1, e2, h]

/-- The pointwise Gaussian-composition identity. -/
theorem pointwise_complete_square {c wn wp : ℝ} (hc : 0 < c) (hwn : 0 < wn)
    (hw : c * wn = wp * (c + wn)) (w A : ℂ) :
    c * ‖w - A‖ ^ 2 + wn * ‖A‖ ^ 2 =
      wp * ‖w‖ ^ 2 + (c + wn) * ‖A - ((c / (c + wn) : ℝ) : ℂ) * w‖ ^ 2 := by
  have hcw : c + wn ≠ 0 := by positivity
  have hwp : wp = c * wn / (c + wn) := by field_simp; linarith
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  rw [hwp]
  field_simp
  ring

end Blocks

section Weights

omit [NeZero L] in
/-- The weight identity of the Gaussian composition (6.1) in fine units:
`(a_{n+1} L^{-2(n+1)})⁻¹ = (a₁ L^{-2(n+1)})⁻¹ + (a_n L^{-2n})⁻¹`, i.e. `a_{n+1} = a₁ a_n / (a_n + a₁ L⁻²)`
(FLUCTUATION (2.9), in the form `1/a_{n+1} = 1/a₁ + L⁻²/a_n`). -/
theorem compWeight_harmonic {a₁ : ℝ} (hL : 2 ≤ L) (ha₁ : 0 < a₁) (n : ℕ) :
    ((compWeight L a₁ (n + 1)) / ((L : ℝ) ^ (n + 1)) ^ 2)⁻¹ =
      (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2)⁻¹ + (compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2)⁻¹ := by
  have h2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have h4 : 1 < (L : ℝ) ^ 2 := by nlinarith
  rw [inv_div, inv_div, inv_div, ← inv_inv (compWeight L a₁ (n + 1)), ← inv_inv (compWeight L a₁ n)]
  rw [div_eq_mul_inv, div_eq_mul_inv, inv_inv, compWeight_inv, compWeight_inv]
  have hne : (1 - (((L : ℝ) ^ 2)⁻¹)) ≠ 0 := by
    have : ((L : ℝ) ^ 2)⁻¹ < 1 := by rw [inv_lt_one₀ (by positivity)]; exact h4
    linarith
  have hne2 : (1 - ((((L : ℝ) ^ (n+1)) ^ 2)⁻¹)) ≠ 0 := by
    have h5 : 1 < ((L : ℝ) ^ (n+1)) ^ 2 := by
      have : (1 : ℝ) < (L : ℝ) ^ (n+1) := one_lt_pow₀ (by linarith) (by omega)
      nlinarith
    have : (((L : ℝ) ^ (n+1)) ^ 2)⁻¹ < 1 := by rw [inv_lt_one₀ (by positivity)]; exact h5
    linarith
  have hne3 : (-1 + (L : ℝ) ^ 2) ≠ 0 := by linarith
  field_simp
  have hinv : (-1 + (L : ℝ) ^ 2)⁻¹ * (-1 + (L : ℝ) ^ 2) = 1 := inv_mul_cancel₀ hne3
  linear_combination ((L : ℝ) ^ 2 * (L : ℝ) ^ (n * 2)) * hinv

omit [NeZero L] in
/-- `c w_n = w_p (c + w_n)` for `c = a₁ L^{-2(n+1)}`, `w_j = a_j L^{-2j}`: the Gaussian composition
`1/w_p = 1/c + 1/w_n`. -/
theorem weight_relation {a₁ : ℝ} (hL : 2 ≤ L) (ha₁ : 0 < a₁) {n : ℕ} (hn : 1 ≤ n) :
    (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2) * (compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) =
      (compWeight L a₁ (n + 1) / ((L : ℝ) ^ (n + 1)) ^ 2) *
        ((a₁ / ((L : ℝ) ^ (n + 1)) ^ 2) + compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hH := compWeight_harmonic (L := L) hL ha₁ n
  have hp0 := compWeight_pos hL ha₁ (show 1 ≤ n + 1 by omega)
  have hwp0 : 0 < compWeight L a₁ (n + 1) / ((L : ℝ) ^ (n + 1)) ^ 2 := by positivity
  set c : ℝ := a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 with hc
  set wn : ℝ := compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2 with hwn
  set wp : ℝ := compWeight L a₁ (n + 1) / ((L : ℝ) ^ (n + 1)) ^ 2 with hwp
  have h1 : wp⁻¹ * (c * wn) = c + wn := by
    rw [hH]
    have hc0 : 0 < c := by positivity
    have hwn0 : 0 < wn := by
      have := compWeight_pos hL ha₁ hn
      positivity
    field_simp
    ring
  have h2 : wp * (wp⁻¹ * (c * wn)) = c * wn := by
    rw [← mul_assoc, mul_inv_cancel₀ hwp0.ne', one_mul]
  rw [← h2, h1]

end Weights

section GaussianComposition

variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}

/-- **The coupling term** `½ a₁ L^{-2p} ∑_x |θ(x) - (Q_p ψ)(x)|²` of `J_k` (FLUCTUATION §2.2,
`½ a L⁻² ‖θ - Qψ‖_L²`), in the fine units of Background (`p = k + 1`): the block-spin field `θ` and
the lifted field `ψ` are functions on the fine torus, `Q_p` is the average over `p`-blocks.  The
`η`-unit expression is `L^{-k(d-2)}` times this one (FLUCTUATION §1.1). -/
noncomputable def coupling (G' : GeneratingSet d L N₀ K ϱ') (a₁ : ℝ) (p : ℕ)
    (θ Ψ : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℝ :=
  (1 / 2) * (a₁ / ((L : ℝ) ^ p) ^ 2) *
    ∑ x, ∑ i, ‖θ x i - blockMean G' p (fun y => Ψ y i) x‖ ^ 2

/-- **The point `Ψ(θ, φ)` of (2.1)**:
`Ψ(θ,φ) = Q_n φ + (a_p/a_n) L^{2(n-p)} (θ - Q_p φ)` (`n = k`, `p = k + 1`), with `f` the extension
of `φ` to the torus. -/
noncomputable def psiStar (G : GeneratingSet d L N₀ K ϱ) (G' : GeneratingSet d L N₀ K ϱ')
    (a : ℕ → ℝ) (n p : ℕ) (θ f : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (x : Torus d (N₀ * L ^ K)) (i : Fin N) : ℂ :=
  blockMean G n (fun y => f y i) x +
    ((a p / a n * (((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ p) ^ 2) : ℝ) : ℂ) *
      (θ x i - blockMean G' p (fun y => f y i) x)

/-- The defect: the non-negative remainder in the Gaussian composition. -/
noncomputable def defect (G : GeneratingSet d L N₀ K ϱ) (G' : GeneratingSet d L N₀ K ϱ')
    (a : ℕ → ℝ) (a₁ : ℝ) (n p : ℕ) (θ Ψ f : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℝ :=
  (1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) * ∑ x, ∑ i,
      ‖(Ψ x i - blockMean G n (fun y => f y i) x) -
        blockMean G' p (fun y => Ψ y i - blockMean G n (fun y => f y i) y) x‖ ^ 2 +
    (1 / 2) * (a₁ / ((L : ℝ) ^ p) ^ 2 + a n / ((L : ℝ) ^ n) ^ 2) * ∑ x, ∑ i,
      ‖blockMean G' p (fun y => Ψ y i - blockMean G n (fun y => f y i) y) x -
        ((a₁ / ((L : ℝ) ^ p) ^ 2 / (a₁ / ((L : ℝ) ^ p) ^ 2 + a n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) *
          (θ x i - blockMean G' p (fun y => f y i) x)‖ ^ 2

/-- The identity of the Gaussian composition, for one component. -/
theorem gaussian_identity_component {a₁ : ℝ} (hL : 2 ≤ L) (ha₁ : 0 < a₁) {n : ℕ} (hn : 1 ≤ n)
    (hp : n + 1 ≤ K) (θ Ψ f : Torus d (N₀ * L ^ K) → ℂ) :
    (1 / 2) * (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2) *
        ∑ x, ‖θ x - blockMean G' (n + 1) Ψ x‖ ^ 2 +
      (1 / 2) * (compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) *
        ∑ x, ‖Ψ x - blockMean G n f x‖ ^ 2 =
    (1 / 2) * (compWeight L a₁ (n + 1) / ((L : ℝ) ^ (n + 1)) ^ 2) *
        ∑ x, ‖θ x - blockMean G' (n + 1) f x‖ ^ 2 +
      ((1 / 2) * (compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) * ∑ x,
        ‖(Ψ x - blockMean G n f x) -
          blockMean G' (n + 1) (fun y => Ψ y - blockMean G n f y) x‖ ^ 2 +
      (1 / 2) * (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 + compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) * ∑ x,
        ‖blockMean G' (n + 1) (fun y => Ψ y - blockMean G n f y) x -
          ((a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 /
            (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 + compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) *
            (θ x - blockMean G' (n + 1) f x)‖ ^ 2) := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  set c : ℝ := a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 with hc
  set wn : ℝ := compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2 with hwn
  set wp : ℝ := compWeight L a₁ (n + 1) / ((L : ℝ) ^ (n + 1)) ^ 2 with hwp
  have hc0 : 0 < c := by positivity
  have hwn0 : 0 < wn := by
    rw [hwn]
    have := compWeight_pos hL ha₁ hn
    positivity
  have hwp0 : 0 < wp := by
    rw [hwp]
    have := compWeight_pos hL ha₁ (show 1 ≤ n + 1 by omega)
    positivity
  have hw : c * wn = wp * (c + wn) := weight_relation hL ha₁ hn
  have hnest : ∀ x, blockMean G' (n + 1) (fun y => Ψ y - blockMean G n f y) x =
      blockMean G' (n + 1) Ψ x - blockMean G' (n + 1) f x := fun x => by
    have e : blockMean G' (n + 1) (fun y => blockMean G n f y) x = blockMean G' (n + 1) f x :=
      blockMean_nested (G := G) (Nat.le_succ n) hp f x
    rw [blockMean_sub, e]
  have hdec := sum_norm_sq_decomp (G := G') hp (fun y => Ψ y - blockMean G n f y)
  have hpt : ∀ x, c * ‖(θ x - blockMean G' (n + 1) f x) -
        blockMean G' (n + 1) (fun y => Ψ y - blockMean G n f y) x‖ ^ 2 +
      wn * ‖blockMean G' (n + 1) (fun y => Ψ y - blockMean G n f y) x‖ ^ 2 =
      wp * ‖θ x - blockMean G' (n + 1) f x‖ ^ 2 + (c + wn) *
        ‖blockMean G' (n + 1) (fun y => Ψ y - blockMean G n f y) x -
          ((c / (c + wn) : ℝ) : ℂ) * (θ x - blockMean G' (n + 1) f x)‖ ^ 2 := fun x =>
    pointwise_complete_square hc0 hwn0 hw _ _
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset (Torus d (N₀ * L ^ K))) = _)
    (fun x (_ : x ∈ (Finset.univ : Finset (Torus d (N₀ * L ^ K)))) => hpt x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hθ : ∀ x, (θ x - blockMean G' (n + 1) f x) -
        blockMean G' (n + 1) (fun y => Ψ y - blockMean G n f y) x =
      θ x - blockMean G' (n + 1) Ψ x := fun x => by rw [hnest]; ring
  simp only [hθ] at hsum
  simp only [hnest] at hdec hsum ⊢
  have hdec2 := congrArg (fun t => wn * t) hdec
  simp only [mul_add] at hdec2
  linarith [hsum, hdec2]

theorem sum_sum_comm' {α β : Type*} [Fintype α] [Fintype β] (F : α → β → ℝ) :
    ∑ x, ∑ i, F x i = ∑ i, ∑ x, F x i := Finset.sum_comm

/-- **The Gaussian composition (FLUCTUATION Lemma 2.2 (a))**, fine units, `p = n + 1`:
`coupling + (level-n term) = (level-(n+1) term) + defect`. -/
theorem coupling_add_level {a₁ : ℝ} (hL : 2 ≤ L) (ha₁ : 0 < a₁) {n : ℕ} (hn : 1 ≤ n)
    (hp : n + 1 ≤ K) (θ Ψ f : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    coupling G' a₁ (n + 1) θ Ψ +
        (1 / 2) * (compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) *
          ∑ x, ∑ i, ‖Ψ x i - blockMean G n (fun y => f y i) x‖ ^ 2 =
      (1 / 2) * (compWeight L a₁ (n + 1) / ((L : ℝ) ^ (n + 1)) ^ 2) *
          ∑ x, ∑ i, ‖θ x i - blockMean G' (n + 1) (fun y => f y i) x‖ ^ 2 +
        defect G G' (compWeight L a₁) a₁ n (n + 1) θ Ψ f := by
  unfold coupling defect
  have e1 := sum_sum_comm'
    (fun x i => ‖θ x i - blockMean G' (n + 1) (fun y => Ψ y i) x‖ ^ 2)
  have e2 := sum_sum_comm'
    (fun x i => ‖Ψ x i - blockMean G n (fun y => f y i) x‖ ^ 2)
  have e3 := sum_sum_comm'
    (fun x i => ‖θ x i - blockMean G' (n + 1) (fun y => f y i) x‖ ^ 2)
  have e4 := sum_sum_comm'
    (fun x i => ‖(Ψ x i - blockMean G n (fun y => f y i) x) -
        blockMean G' (n + 1) (fun y => Ψ y i - blockMean G n (fun y => f y i) y) x‖ ^ 2)
  have e5 := sum_sum_comm'
    (fun x i => ‖blockMean G' (n + 1) (fun y => Ψ y i - blockMean G n (fun y => f y i) y) x -
        ((a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 /
          (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 + compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) *
          (θ x i - blockMean G' (n + 1) (fun y => f y i) x)‖ ^ 2)
  beta_reduce at e1 e2 e3 e4 e5
  rw [e1, e2, e3, e4, e5]
  have key := fun i => gaussian_identity_component (G := G) (G' := G') hL ha₁ hn hp
    (fun x => θ x i) (fun x => Ψ x i) (fun x => f x i)
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => key i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  linarith [hs]

omit [NeZero L] in
theorem lambda_eq {a₁ : ℝ} (hL : 2 ≤ L) (ha₁ : 0 < a₁) {n : ℕ} (hn : 1 ≤ n) :
    a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 /
        (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 + compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) =
      compWeight L a₁ (n + 1) / compWeight L a₁ n *
        (((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ (n + 1)) ^ 2) := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hn0 := compWeight_pos hL ha₁ hn
  have hp0 := compWeight_pos hL ha₁ (show 1 ≤ n + 1 by omega)
  set c : ℝ := a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 with hc
  set wn : ℝ := compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2 with hwn
  set wp : ℝ := compWeight L a₁ (n + 1) / ((L : ℝ) ^ (n + 1)) ^ 2 with hwp
  have hc0 : 0 < c := by positivity
  have hwn0 : 0 < wn := by positivity
  have hwp0 : 0 < wp := by positivity
  have hw : c * wn = wp * (c + wn) := weight_relation hL ha₁ hn
  have e : compWeight L a₁ (n + 1) / compWeight L a₁ n *
      (((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ (n + 1)) ^ 2) = wp / wn := by
    rw [hwp, hwn]; field_simp
  rw [e]
  field_simp
  linarith

theorem defect_nonneg {a₁ : ℝ} (hL : 2 ≤ L) (ha₁ : 0 < a₁) {n : ℕ} (hn : 1 ≤ n)
    (θ Ψ f : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    0 ≤ defect G G' (compWeight L a₁) a₁ n (n + 1) θ Ψ f := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hn0 := compWeight_pos hL ha₁ hn
  unfold defect
  have : 0 < compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2 := by positivity
  have : 0 < a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 := by positivity
  positivity

theorem sum_sum_sq_eq_zero {α β : Type*} [Fintype α] [Fintype β] (F : α → β → ℂ)
    (h : ∑ x, ∑ i, ‖F x i‖ ^ 2 = 0) (x : α) (i : β) : F x i = 0 := by
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
    Finset.sum_nonneg (fun i _ => sq_nonneg ‖F x i‖))).1 h x (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖F x i‖)).1 h1 i
    (Finset.mem_univ _)
  simpa using h2

/-- **Lemma 2.2 (a), the minimiser**: the defect vanishes exactly at `Ψ = Ψ(θ, φ)` of (2.1)
(for a block field `θ`). -/
theorem defect_eq_zero_iff {a₁ : ℝ} (hL : 2 ≤ L) (ha₁ : 0 < a₁) {n : ℕ} (hn : 1 ≤ n)
    (hp : n + 1 ≤ K) (θ Ψ f : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (hθ : ∀ x y i, y ∈ G'.blk (n + 1) x → θ y i = θ x i) :
    defect G G' (compWeight L a₁) a₁ n (n + 1) θ Ψ f = 0 ↔
      ∀ x i, Ψ x i = psiStar G G' (compWeight L a₁) n (n + 1) θ f x i := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hn0 := compWeight_pos hL ha₁ hn
  have hwn0 : 0 < compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2 := by positivity
  have hc0 : 0 < a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 := by positivity
  have hlam := lambda_eq hL ha₁ hn
  unfold defect psiStar
  rw [← hlam]
  constructor
  · intro h0
    have hS1 : 0 ≤ ∑ x, ∑ i, ‖(Ψ x i - blockMean G n (fun y => f y i) x) -
        blockMean G' (n + 1) (fun y => Ψ y i - blockMean G n (fun y => f y i) y) x‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hS2 : 0 ≤ ∑ x, ∑ i, ‖blockMean G' (n + 1) (fun y => Ψ y i -
        blockMean G n (fun y => f y i) y) x -
        ((a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 / (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 +
          compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) *
          (θ x i - blockMean G' (n + 1) (fun y => f y i) x)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hc1 : 0 ≤ (1 / 2) * (compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) := by positivity
    have hc2 : 0 ≤ (1 / 2) * (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 +
        compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) := by positivity
    have e1 : ∑ x, ∑ i, ‖(Ψ x i - blockMean G n (fun y => f y i) x) -
        blockMean G' (n + 1) (fun y => Ψ y i - blockMean G n (fun y => f y i) y) x‖ ^ 2 = 0 := by
      have := mul_nonneg hc1 hS1
      have := mul_nonneg hc2 hS2
      have h3 : (1 / 2) * (compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) * ∑ x, ∑ i,
          ‖(Ψ x i - blockMean G n (fun y => f y i) x) -
          blockMean G' (n + 1) (fun y => Ψ y i - blockMean G n (fun y => f y i) y) x‖ ^ 2 = 0 := by
        linarith
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h (by positivity)
      · exact h
    have e2 : ∑ x, ∑ i, ‖blockMean G' (n + 1) (fun y => Ψ y i -
        blockMean G n (fun y => f y i) y) x -
        ((a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 / (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 +
          compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) *
          (θ x i - blockMean G' (n + 1) (fun y => f y i) x)‖ ^ 2 = 0 := by
      have := mul_nonneg hc1 hS1
      have := mul_nonneg hc2 hS2
      have h3 : (1 / 2) * (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 +
          compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) * ∑ x, ∑ i, ‖blockMean G' (n + 1) (fun y => Ψ y i -
        blockMean G n (fun y => f y i) y) x -
        ((a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 / (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 +
          compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) *
          (θ x i - blockMean G' (n + 1) (fun y => f y i) x)‖ ^ 2 = 0 := by
        linarith
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h (by positivity)
      · exact h
    intro x i
    have h1 := sum_sum_sq_eq_zero _ e1 x i
    have h2 := sum_sum_sq_eq_zero _ e2 x i
    linear_combination h1 + h2
  · intro hΨ
    have hw : ∀ x i, ∀ y ∈ G'.blk (n + 1) x,
        θ y i - blockMean G' (n + 1) (fun z => f z i) y =
          θ x i - blockMean G' (n + 1) (fun z => f z i) x := fun x i y hy => by
      rw [hθ x y i hy, blockMean_blk_const (G := G') (fun z => f z i) x y hy]
    have hA : ∀ y i, Ψ y i - blockMean G n (fun z => f z i) y =
        ((a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 / (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 +
          compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) *
          (θ y i - blockMean G' (n + 1) (fun z => f z i) y) := fun y i => by
      rw [hΨ y i]; ring
    have hAbar : ∀ x i, blockMean G' (n + 1) (fun y => Ψ y i - blockMean G n (fun z => f z i) y) x =
        ((a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 / (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 +
          compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) *
          (θ x i - blockMean G' (n + 1) (fun z => f z i) x) := fun x i => by
      have : (fun y => Ψ y i - blockMean G n (fun z => f z i) y) = fun y =>
          ((a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 / (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 +
            compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) *
            (θ y i - blockMean G' (n + 1) (fun z => f z i) y) := funext fun y => hA y i
      rw [this, blockMean_smul, blockMean_of_blk_const hp _ x (hw x i)]
    have z1 : ∀ x i, (Ψ x i - blockMean G n (fun y => f y i) x) -
        blockMean G' (n + 1) (fun y => Ψ y i - blockMean G n (fun y => f y i) y) x = 0 :=
      fun x i => by rw [hAbar, hA]; ring
    have z2 : ∀ x i, blockMean G' (n + 1) (fun y => Ψ y i - blockMean G n (fun y => f y i) y) x -
        ((a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 / (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 +
          compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) *
          (θ x i - blockMean G' (n + 1) (fun y => f y i) x) = 0 :=
      fun x i => by rw [hAbar]; ring
    simp only [z1, z2]
    simp

end GaussianComposition



section GaussianPart

variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'} {a₁ : ℝ} {n : ℕ}

/-- The level energy `½ a_n L^{-2n} ∑ |θ - Q_n φ|²` (fine units; `n = k` gives
`½ a_k ‖θ - Q_k φ‖²` and `n = k + 1` gives `½ a_{k+1} L⁻² ‖θ - Q_{k+1} φ‖_L²` of FLUCTUATION §2.2). -/
noncomputable def levelEnergy (G : GeneratingSet d L N₀ K ϱ) (a : ℕ → ℝ) (n : ℕ)
    (θ f : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℝ :=
  (1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) *
    ∑ x, ∑ i, ‖θ x i - blockMean G n (fun y => f y i) x‖ ^ 2

omit [NeZero N₀] [NeZero L] in
/-- **Lemma 2.2 (a), the recursion**: `a_{n+1} = a₁ a_n / (a_n + a₁ L⁻²)` (P4 (2.9)), `n ≥ 1`. -/
theorem compWeight_succ (hL : 2 ≤ L) (ha₁ : 0 < a₁) (hn : 1 ≤ n) :
    compWeight L a₁ (n + 1) =
      a₁ * compWeight L a₁ n / (compWeight L a₁ n + a₁ * ((L : ℝ) ^ 2)⁻¹) := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hn0 := compWeight_pos hL ha₁ hn
  have hp0 := compWeight_pos hL ha₁ (show 1 ≤ n + 1 by omega)
  have hw := weight_relation (L := L) hL ha₁ hn
  have h1 : (0 : ℝ) < ((L : ℝ) ^ 2)⁻¹ := by positivity
  rw [eq_div_iff (by positivity)]
  have e1 : ((L : ℝ) ^ (n + 1)) ^ 2 = ((L : ℝ) ^ n) ^ 2 * (L : ℝ) ^ 2 := by ring
  have hLn : (0 : ℝ) < ((L : ℝ) ^ n) ^ 2 := by positivity
  rw [e1] at hw
  field_simp at hw
  field_simp
  nlinarith [hw]

/-- **Lemma 2.2 (a), the Gaussian composition.**  For `θ` constant on the `(n+1)`-blocks and every
field `φ` (extended to the torus as `f`), and every `Ψ`:
`½ a_{n+1} L^{-2(n+1)} ∑ |θ - Q_{n+1} f|² ≤ ½ a₁ L^{-2(n+1)} ∑ |θ - Q_{n+1} Ψ|² +
 ½ a_n L^{-2n} ∑ |Ψ - Q_n f|²`, with equality exactly when `Ψ = Ψ(θ, φ)` (`psiStar`, (2.1)). -/
theorem gaussianComposition (hL : 2 ≤ L) (ha₁ : 0 < a₁) (hn : 1 ≤ n) (hp : n + 1 ≤ K)
    (θ f : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (hθ : ∀ x y i, y ∈ G'.blk (n + 1) x → θ y i = θ x i) (Ψ : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    levelEnergy G' (compWeight L a₁) (n + 1) θ f ≤
        coupling G' a₁ (n + 1) θ Ψ + levelEnergy G (compWeight L a₁) n Ψ f ∧
      (coupling G' a₁ (n + 1) θ Ψ + levelEnergy G (compWeight L a₁) n Ψ f =
          levelEnergy G' (compWeight L a₁) (n + 1) θ f ↔
        ∀ x i, Ψ x i = psiStar G G' (compWeight L a₁) n (n + 1) θ f x i) := by
  have key := coupling_add_level (G := G) (G' := G') (a₁ := a₁) hL ha₁ hn hp θ Ψ f
  have h0 := defect_nonneg (G := G) (G' := G') (a₁ := a₁) hL ha₁ hn θ Ψ f
  have hz := defect_eq_zero_iff (G := G) (G' := G') hL ha₁ hn hp θ Ψ f hθ
  unfold levelEnergy
  refine ⟨by linarith, ?_⟩
  rw [← hz]
  constructor <;> intro h <;> linarith

end GaussianPart

end Balaban.Fluctuation
