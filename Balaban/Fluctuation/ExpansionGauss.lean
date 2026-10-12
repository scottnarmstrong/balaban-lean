module

public import Balaban.Fluctuation.CriticalPointGauss
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Lemma 2.3 (a), the algebra: the Gaussian composition with the bilinear product

The complex-data counterpart of `CriticalPointGauss`: for the bilinear product `u * v` in place of
`‖u‖²`, and a block field `θ`,
`couplingC θ Ψ + levelEnergyC_n Ψ f = levelEnergyC_{n+1} θ f + defectC`
(`coupling_add_levelC`), with `defectC = ½ w_n ∑ u·u + ½ c ∑ (Q_{n+1} u)·(Q_{n+1} u)`,
`u = Ψ - Ψ(θ, f)` (`psiStar`).  This is the completion of the square behind the chord identity
(2.3); `sum_sq_decomp_bil` is the orthogonal decomposition along `p`-block averages.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

section Bilinear

variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}

/-- Orthogonal decomposition along `p`-block averages, for the bilinear product. -/
theorem sum_sq_decomp_bil {p : ℕ} (hp : p ≤ K) (A : Torus d (N₀ * L ^ K) → ℂ) :
    ∑ x, A x * A x = ∑ x, (A x - blockMean G p A x) * (A x - blockMean G p A x) +
      ∑ x, blockMean G p A x * blockMean G p A x := by
  have hn : ∀ z : Torus d (N₀ * L ^ K), (fun _ => p) z ≤ K := fun _ => hp
  have h1 : ∑ z ∈ (Finset.univ : Finset (Torus d (N₀ * L ^ K))),
      blockMean G ((fun _ => p) z) (fun y => blockMean G p A y * A y) z =
      ∑ z ∈ (Finset.univ : Finset (Torus d (N₀ * L ^ K))),
        (fun y => blockMean G p A y * A y) z :=
    sum_blockMean_nested G Finset.univ (fun _ => p) hn _ (fun _ _ _ _ =>
      ⟨Finset.mem_univ _, rfl⟩)
  have h2 : ∀ x, blockMean G p (fun y => blockMean G p A y * A y) x =
      blockMean G p A x * blockMean G p A x := fun x =>
    blockMean_mul_const _ _ (fun x y hy => blockMean_blk_const A x y hy) x
  simp only [h2] at h1
  have h3 : ∀ x, A x * A x = (A x - blockMean G p A x) * (A x - blockMean G p A x) +
      blockMean G p A x * blockMean G p A x +
      2 * (blockMean G p A x * A x - blockMean G p A x * blockMean G p A x) := fun x => by ring
  simp only [h3, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [h1]; ring

/-- The pointwise Gaussian-composition identity, for the bilinear product. -/
theorem pointwise_bil {c wn wp lam : ℝ} (hlam : (c + wn) * lam = c) (hwp : wp = c * (1 - lam))
    (w A : ℂ) :
    (c : ℂ) * ((w - A) * (w - A)) + (wn : ℂ) * (A * A) =
      (wp : ℂ) * (w * w) + ((c + wn : ℝ) : ℂ) * ((A - (lam : ℂ) * w) * (A - (lam : ℂ) * w)) := by
  have h1 : ((c : ℂ) + wn) * lam = c := by exact_mod_cast hlam
  have h2 : (wp : ℂ) = c * (1 - lam) := by exact_mod_cast hwp
  push_cast
  rw [h2]
  linear_combination (2 * w * A - lam * w ^ 2) * h1

/-- The Gaussian composition for one component, bilinear form. -/
theorem gaussian_component_bil {c wn wp lam : ℝ} (hlam : (c + wn) * lam = c)
    (hwp : wp = c * (1 - lam)) {n p : ℕ} (hnp : n ≤ p) (hp : p ≤ K)
    (θ Ψ f : Torus d (N₀ * L ^ K) → ℂ)
    (hθ : ∀ x y, y ∈ G'.blk p x → θ y = θ x) :
    (c : ℂ) * ∑ x, (θ x - blockMean G' p Ψ x) * (θ x - blockMean G' p Ψ x) +
        (wn : ℂ) * ∑ x, (Ψ x - blockMean G n f x) * (Ψ x - blockMean G n f x) =
      (wp : ℂ) * ∑ x, (θ x - blockMean G' p f x) * (θ x - blockMean G' p f x) +
        ((wn : ℂ) * ∑ x, (Ψ x - blockMean G n f x - (lam : ℂ) * (θ x - blockMean G' p f x)) *
            (Ψ x - blockMean G n f x - (lam : ℂ) * (θ x - blockMean G' p f x)) +
          (c : ℂ) * ∑ x, blockMean G' p (fun y => Ψ y - blockMean G n f y -
              (lam : ℂ) * (θ y - blockMean G' p f y)) x *
            blockMean G' p (fun y => Ψ y - blockMean G n f y -
              (lam : ℂ) * (θ y - blockMean G' p f y)) x) := by
  set A : Torus d (N₀ * L ^ K) → ℂ := fun y => Ψ y - blockMean G n f y with hA
  set w : Torus d (N₀ * L ^ K) → ℂ := fun y => θ y - blockMean G' p f y with hw
  have hwc : ∀ x y, y ∈ G'.blk p x → w y = w x := fun x y hy => by
    simp only [hw]
    rw [hθ x y hy, blockMean_blk_const (G := G') f x y hy]
  have hAbar : ∀ x, blockMean G' p A x = blockMean G' p Ψ x - blockMean G' p f x := fun x => by
    have e : blockMean G' p (fun y => blockMean G n f y) x = blockMean G' p f x :=
      blockMean_nested (G := G) hnp hp f x
    simp only [hA]
    rw [blockMean_sub, e]
  have hQu : ∀ x, blockMean G' p (fun y => A y - (lam : ℂ) * w y) x =
      blockMean G' p A x - (lam : ℂ) * w x := fun x => by
    rw [blockMean_sub, blockMean_smul, blockMean_of_blk_const hp w x (hwc x)]
  have hdA := sum_sq_decomp_bil (G := G') hp A
  have hdu := sum_sq_decomp_bil (G := G') hp (fun y => A y - (lam : ℂ) * w y)
  simp only [hQu] at hdu
  have hpt2 : ∀ x, (A x - (lam : ℂ) * w x - (blockMean G' p A x - (lam : ℂ) * w x)) *
      (A x - (lam : ℂ) * w x - (blockMean G' p A x - (lam : ℂ) * w x)) =
      (A x - blockMean G' p A x) * (A x - blockMean G' p A x) := fun x => by ring
  simp only [hpt2] at hdu
  have hpt : ∀ x, (c : ℂ) * ((w x - blockMean G' p A x) * (w x - blockMean G' p A x)) +
      (wn : ℂ) * (blockMean G' p A x * blockMean G' p A x) =
      (wp : ℂ) * (w x * w x) + ((c + wn : ℝ) : ℂ) *
        ((blockMean G' p A x - (lam : ℂ) * w x) * (blockMean G' p A x - (lam : ℂ) * w x)) :=
    fun x => pointwise_bil hlam hwp (w x) (blockMean G' p A x)
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset (Torus d (N₀ * L ^ K))) = _)
    (fun x (_ : x ∈ (Finset.univ : Finset (Torus d (N₀ * L ^ K)))) => hpt x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hθQ : ∀ x, θ x - blockMean G' p Ψ x = w x - blockMean G' p A x := fun x => by
    rw [hAbar]; simp only [hw]; ring
  have hQu2 : ∀ x, blockMean G' p (fun y => Ψ y - blockMean G n f y -
      (lam : ℂ) * (θ y - blockMean G' p f y)) x = blockMean G' p A x - (lam : ℂ) * w x := hQu
  simp only [hθQ, hQu2]
  push_cast at hsum
  linear_combination hsum + (wn : ℂ) * hdA - (wn : ℂ) * hdu

variable {a₁ : ℝ} {n : ℕ}

/-- The coupling term `½ a₁ L^{-2p} ∑ (θ - Q_p Ψ)·(θ - Q_p Ψ)` with the bilinear product
(`coupling` has the norms; they agree on real fields). -/
noncomputable def couplingC (G' : GeneratingSet d L N₀ K ϱ') (a₁ : ℝ) (p : ℕ)
    (θ Ψ : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  (((1 / 2) * (a₁ / ((L : ℝ) ^ p) ^ 2) : ℝ) : ℂ) *
    ∑ x, ∑ i, (θ x i - blockMean G' p (fun y => Ψ y i) x) *
      (θ x i - blockMean G' p (fun y => Ψ y i) x)

/-- The level energy with the bilinear product. -/
noncomputable def levelEnergyC (G : GeneratingSet d L N₀ K ϱ) (a : ℕ → ℝ) (n : ℕ)
    (θ f : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  (((1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) *
    ∑ x, ∑ i, (θ x i - blockMean G n (fun y => f y i) x) *
      (θ x i - blockMean G n (fun y => f y i) x)

/-- The defect with the bilinear product: `½ w_n ∑ u·u + ½ c ∑ (Q_{n+1} u)·(Q_{n+1} u)` with
`u = Ψ - Ψ(θ, φ)`. -/
noncomputable def defectC (G : GeneratingSet d L N₀ K ϱ) (G' : GeneratingSet d L N₀ K ϱ')
    (a : ℕ → ℝ) (a₁ : ℝ) (n : ℕ) (θ Ψ f : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  (((1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) * ∑ x, ∑ i,
      (Ψ x i - psiStar G G' a n (n + 1) θ f x i) * (Ψ x i - psiStar G G' a n (n + 1) θ f x i) +
    (((1 / 2) * (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2) : ℝ) : ℂ) * ∑ x, ∑ i,
      blockMean G' (n + 1) (fun y => Ψ y i - psiStar G G' a n (n + 1) θ f y i) x *
        blockMean G' (n + 1) (fun y => Ψ y i - psiStar G G' a n (n + 1) θ f y i) x

/-- **The Gaussian composition, bilinear form**: for a block field `θ`,
`coupling + level_n = level_{n+1} + defect`. -/
theorem coupling_add_levelC (hL : 2 ≤ L) (ha₁ : 0 < a₁) (hn : 1 ≤ n) (hp : n + 1 ≤ K)
    (θ Ψ f : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (hθ : ∀ x y i, y ∈ G'.blk (n + 1) x → θ y i = θ x i) :
    couplingC G' a₁ (n + 1) θ Ψ + levelEnergyC G (compWeight L a₁) n Ψ f =
      levelEnergyC G' (compWeight L a₁) (n + 1) θ f +
        defectC G G' (compWeight L a₁) a₁ n θ Ψ f := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hn0 := compWeight_pos hL ha₁ hn
  have hwn0 : 0 < compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2 := by positivity
  have hc0 : 0 < a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 := by positivity
  have hw := weight_relation (L := L) hL ha₁ hn
  have hlam0 := lambda_eq hL ha₁ hn
  set c : ℝ := a₁ / ((L : ℝ) ^ (n + 1)) ^ 2 with hc
  set wn : ℝ := compWeight L a₁ n / ((L : ℝ) ^ n) ^ 2 with hwn
  set wp : ℝ := compWeight L a₁ (n + 1) / ((L : ℝ) ^ (n + 1)) ^ 2 with hwp
  have hcw : c + wn ≠ 0 := by positivity
  have hlam : (c + wn) * (c / (c + wn)) = c := by field_simp
  have hwp' : wp = c * (1 - c / (c + wn)) := by
    field_simp
    linarith
  have key := fun i => gaussian_component_bil (G := G) (G' := G') hlam hwp' (Nat.le_succ n) hp
    (fun x => θ x i) (fun x => Ψ x i) (fun x => f x i) (fun x y hy => hθ x y i hy)
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => key i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hu : ∀ x i, Ψ x i - psiStar G G' (compWeight L a₁) n (n + 1) θ f x i =
      Ψ x i - blockMean G n (fun y => f y i) x - ((c / (c + wn) : ℝ) : ℂ) *
        (θ x i - blockMean G' (n + 1) (fun y => f y i) x) := fun x i => by
    unfold psiStar
    rw [← hlam0]
    ring
  unfold couplingC levelEnergyC defectC
  simp only [hu]
  have sc : ∀ F : Torus d (N₀ * L ^ K) → Fin N → ℂ, ∑ x, ∑ i, F x i = ∑ i, ∑ x, F x i :=
    fun F => Finset.sum_comm
  have e1 := sc (fun x i => (θ x i - blockMean G' (n + 1) (fun y => Ψ y i) x) *
    (θ x i - blockMean G' (n + 1) (fun y => Ψ y i) x))
  have e2 := sc (fun x i => (Ψ x i - blockMean G n (fun y => f y i) x) *
    (Ψ x i - blockMean G n (fun y => f y i) x))
  have e3 := sc (fun x i => (θ x i - blockMean G' (n + 1) (fun y => f y i) x) *
    (θ x i - blockMean G' (n + 1) (fun y => f y i) x))
  have e4 := sc (fun x i => (Ψ x i - blockMean G n (fun y => f y i) x - ((c / (c + wn) : ℝ) : ℂ) *
        (θ x i - blockMean G' (n + 1) (fun y => f y i) x)) *
      (Ψ x i - blockMean G n (fun y => f y i) x - ((c / (c + wn) : ℝ) : ℂ) *
        (θ x i - blockMean G' (n + 1) (fun y => f y i) x)))
  have e5 := sc (fun x i => blockMean G' (n + 1) (fun y => Ψ y i - blockMean G n (fun y => f y i) y -
      ((c / (c + wn) : ℝ) : ℂ) * (θ y i - blockMean G' (n + 1) (fun y => f y i) y)) x *
    blockMean G' (n + 1) (fun y => Ψ y i - blockMean G n (fun y => f y i) y -
      ((c / (c + wn) : ℝ) : ℂ) * (θ y i - blockMean G' (n + 1) (fun y => f y i) y)) x)
  beta_reduce at e1 e2 e3 e4 e5
  rw [e1, e2, e3, e4, e5]
  simp only [← hc, ← hwn, ← hwp]
  clear_value c wn wp
  push_cast at hs ⊢
  linear_combination (1 / 2 : ℂ) * hs

end Bilinear

end Balaban.Fluctuation
