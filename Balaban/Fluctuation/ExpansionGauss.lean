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
(2.3); `sum_sq_decomp_bil` is the orthogonal decomposition along `p`-block averages.  The cores
`sum_sq_decomp_bil_on`, `gaussian_component_bil_on`, `couplingCOn`, `levelEnergyCOn`, `defectCOn`,
`coupling_add_levelC_on` sum over a union `S` of blocks (the new region of a step on a region), the
whole torus being the instance; `couplingCOn_congr_left`, `levelEnergyCOn_congr_left`,
`defectCOn_congr_left`: they read the block field only on `S`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

section Bilinear

variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}

/-- **Orthogonal decomposition along `p`-block averages on a union `S` of `p`-blocks**, bilinear
product (core of `sum_sq_decomp_bil`). -/
theorem sum_sq_decomp_bil_on {p : ℕ} (hp : p ≤ K) (S : Finset (Torus d (N₀ * L ^ K)))
    (hS : ∀ z ∈ S, ∀ y ∈ G.blk p z, y ∈ S) (A : Torus d (N₀ * L ^ K) → ℂ) :
    ∑ x ∈ S, A x * A x = ∑ x ∈ S, (A x - blockMean G p A x) * (A x - blockMean G p A x) +
      ∑ x ∈ S, blockMean G p A x * blockMean G p A x := by
  have hn : ∀ z : Torus d (N₀ * L ^ K), (fun _ => p) z ≤ K := fun _ => hp
  have h1 : ∑ z ∈ S,
      blockMean G ((fun _ => p) z) (fun y => blockMean G p A y * A y) z =
      ∑ z ∈ S,
        (fun y => blockMean G p A y * A y) z :=
    sum_blockMean_nested G S (fun _ => p) hn _ (fun z hz y hy => ⟨hS z hz y hy, rfl⟩)
  have h2 : ∀ x, blockMean G p (fun y => blockMean G p A y * A y) x =
      blockMean G p A x * blockMean G p A x := fun x =>
    blockMean_mul_const _ _ (fun x y hy => blockMean_blk_const A x y hy) x
  simp only [h2] at h1
  have h3 : ∀ x, A x * A x = (A x - blockMean G p A x) * (A x - blockMean G p A x) +
      blockMean G p A x * blockMean G p A x +
      2 * (blockMean G p A x * A x - blockMean G p A x * blockMean G p A x) := fun x => by ring
  simp only [h3, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [h1]; ring

/-- Orthogonal decomposition along `p`-block averages, for the bilinear product. -/
theorem sum_sq_decomp_bil {p : ℕ} (hp : p ≤ K) (A : Torus d (N₀ * L ^ K) → ℂ) :
    ∑ x, A x * A x = ∑ x, (A x - blockMean G p A x) * (A x - blockMean G p A x) +
      ∑ x, blockMean G p A x * blockMean G p A x :=
  sum_sq_decomp_bil_on hp Finset.univ (fun _ _ _ _ => Finset.mem_univ _) A

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

/-- **The Gaussian composition for one component on a union `S` of `p`-blocks**, bilinear form (core
of `gaussian_component_bil`). -/
theorem gaussian_component_bil_on {c wn wp lam : ℝ} (hlam : (c + wn) * lam = c)
    (hwp : wp = c * (1 - lam)) {n p : ℕ} (hnp : n ≤ p) (hp : p ≤ K)
    (S : Finset (Torus d (N₀ * L ^ K))) (hS : ∀ z ∈ S, ∀ y ∈ G'.blk p z, y ∈ S)
    (θ Ψ f : Torus d (N₀ * L ^ K) → ℂ)
    (hθ : ∀ x y, y ∈ G'.blk p x → θ y = θ x) :
    (c : ℂ) * ∑ x ∈ S, (θ x - blockMean G' p Ψ x) * (θ x - blockMean G' p Ψ x) +
        (wn : ℂ) * ∑ x ∈ S, (Ψ x - blockMean G n f x) * (Ψ x - blockMean G n f x) =
      (wp : ℂ) * ∑ x ∈ S, (θ x - blockMean G' p f x) * (θ x - blockMean G' p f x) +
        ((wn : ℂ) * ∑ x ∈ S, (Ψ x - blockMean G n f x - (lam : ℂ) * (θ x - blockMean G' p f x)) *
            (Ψ x - blockMean G n f x - (lam : ℂ) * (θ x - blockMean G' p f x)) +
          (c : ℂ) * ∑ x ∈ S, blockMean G' p (fun y => Ψ y - blockMean G n f y -
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
  have hdA := sum_sq_decomp_bil_on (G := G') hp S hS A
  have hdu := sum_sq_decomp_bil_on (G := G') hp S hS (fun y => A y - (lam : ℂ) * w y)
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
  have hsum := Finset.sum_congr (rfl : S = _) (fun x (_ : x ∈ S) => hpt x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hθQ : ∀ x, θ x - blockMean G' p Ψ x = w x - blockMean G' p A x := fun x => by
    rw [hAbar]; simp only [hw]; ring
  have hQu2 : ∀ x, blockMean G' p (fun y => Ψ y - blockMean G n f y -
      (lam : ℂ) * (θ y - blockMean G' p f y)) x = blockMean G' p A x - (lam : ℂ) * w x := hQu
  simp only [hθQ, hQu2]
  push_cast at hsum
  linear_combination hsum + (wn : ℂ) * hdA - (wn : ℂ) * hdu

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
              (lam : ℂ) * (θ y - blockMean G' p f y)) x) :=
  gaussian_component_bil_on hlam hwp hnp hp Finset.univ (fun _ _ _ _ => Finset.mem_univ _) θ Ψ f hθ

variable {a₁ : ℝ} {n : ℕ}

/-- **The coupling term on a set `S` of sites**, bilinear product (core of `couplingC`). -/
noncomputable def couplingCOn (S : Finset (Torus d (N₀ * L ^ K))) (G' : GeneratingSet d L N₀ K ϱ')
    (a₁ : ℝ) (p : ℕ) (θ Ψ : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  (((1 / 2) * (a₁ / ((L : ℝ) ^ p) ^ 2) : ℝ) : ℂ) *
    ∑ x ∈ S, ∑ i, (θ x i - blockMean G' p (fun y => Ψ y i) x) *
      (θ x i - blockMean G' p (fun y => Ψ y i) x)

/-- The coupling term `½ a₁ L^{-2p} ∑ (θ - Q_p Ψ)·(θ - Q_p Ψ)` with the bilinear product
(`coupling` has the norms; they agree on real fields). -/
noncomputable def couplingC (G' : GeneratingSet d L N₀ K ϱ') (a₁ : ℝ) (p : ℕ)
    (θ Ψ : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  couplingCOn Finset.univ G' a₁ p θ Ψ

/-- **The level energy on a set `S` of sites**, bilinear product (core of `levelEnergyC`). -/
noncomputable def levelEnergyCOn (S : Finset (Torus d (N₀ * L ^ K))) (G : GeneratingSet d L N₀ K ϱ)
    (a : ℕ → ℝ) (n : ℕ) (θ f : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  (((1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) *
    ∑ x ∈ S, ∑ i, (θ x i - blockMean G n (fun y => f y i) x) *
      (θ x i - blockMean G n (fun y => f y i) x)

/-- The level energy with the bilinear product. -/
noncomputable def levelEnergyC (G : GeneratingSet d L N₀ K ϱ) (a : ℕ → ℝ) (n : ℕ)
    (θ f : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  levelEnergyCOn Finset.univ G a n θ f

/-- **The defect on a set `S` of sites**, bilinear product (core of `defectC`). -/
noncomputable def defectCOn (S : Finset (Torus d (N₀ * L ^ K))) (G : GeneratingSet d L N₀ K ϱ)
    (G' : GeneratingSet d L N₀ K ϱ') (a : ℕ → ℝ) (a₁ : ℝ) (n : ℕ)
    (θ Ψ f : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  (((1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) * ∑ x ∈ S, ∑ i,
      (Ψ x i - psiStar G G' a n (n + 1) θ f x i) * (Ψ x i - psiStar G G' a n (n + 1) θ f x i) +
    (((1 / 2) * (a₁ / ((L : ℝ) ^ (n + 1)) ^ 2) : ℝ) : ℂ) * ∑ x ∈ S, ∑ i,
      blockMean G' (n + 1) (fun y => Ψ y i - psiStar G G' a n (n + 1) θ f y i) x *
        blockMean G' (n + 1) (fun y => Ψ y i - psiStar G G' a n (n + 1) θ f y i) x

/-- The defect with the bilinear product: `½ w_n ∑ u·u + ½ c ∑ (Q_{n+1} u)·(Q_{n+1} u)` with
`u = Ψ - Ψ(θ, φ)`. -/
noncomputable def defectC (G : GeneratingSet d L N₀ K ϱ) (G' : GeneratingSet d L N₀ K ϱ')
    (a : ℕ → ℝ) (a₁ : ℝ) (n : ℕ) (θ Ψ f : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  defectCOn Finset.univ G G' a a₁ n θ Ψ f

/-- **The Gaussian composition on a union `S` of `(n+1)`-blocks, bilinear form** (core of
`coupling_add_levelC`): for a block field `θ`,
`coupling + level_n = level_{n+1} + defect`. -/
theorem coupling_add_levelC_on (hL : 2 ≤ L) (ha₁ : 0 < a₁) (hn : 1 ≤ n) (hp : n + 1 ≤ K)
    (S : Finset (Torus d (N₀ * L ^ K))) (hS : ∀ z ∈ S, ∀ y ∈ G'.blk (n + 1) z, y ∈ S)
    (θ Ψ f : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (hθ : ∀ x y i, y ∈ G'.blk (n + 1) x → θ y i = θ x i) :
    couplingCOn S G' a₁ (n + 1) θ Ψ + levelEnergyCOn S G (compWeight L a₁) n Ψ f =
      levelEnergyCOn S G' (compWeight L a₁) (n + 1) θ f +
        defectCOn S G G' (compWeight L a₁) a₁ n θ Ψ f := by
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
  have key := fun i => gaussian_component_bil_on (G := G) (G' := G') hlam hwp' (Nat.le_succ n) hp S hS
    (fun x => θ x i) (fun x => Ψ x i) (fun x => f x i) (fun x y hy => hθ x y i hy)
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => key i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hu : ∀ x i, Ψ x i - psiStar G G' (compWeight L a₁) n (n + 1) θ f x i =
      Ψ x i - blockMean G n (fun y => f y i) x - ((c / (c + wn) : ℝ) : ℂ) *
        (θ x i - blockMean G' (n + 1) (fun y => f y i) x) := fun x i => by
    unfold psiStar
    rw [← hlam0]
    ring
  unfold couplingCOn levelEnergyCOn defectCOn
  simp only [hu]
  have sc : ∀ F : Torus d (N₀ * L ^ K) → Fin N → ℂ, ∑ x ∈ S, ∑ i, F x i = ∑ i, ∑ x ∈ S, F x i :=
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

/-- **The Gaussian composition, bilinear form**: for a block field `θ`,
`coupling + level_n = level_{n+1} + defect`. -/
theorem coupling_add_levelC (hL : 2 ≤ L) (ha₁ : 0 < a₁) (hn : 1 ≤ n) (hp : n + 1 ≤ K)
    (θ Ψ f : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (hθ : ∀ x y i, y ∈ G'.blk (n + 1) x → θ y i = θ x i) :
    couplingC G' a₁ (n + 1) θ Ψ + levelEnergyC G (compWeight L a₁) n Ψ f =
      levelEnergyC G' (compWeight L a₁) (n + 1) θ f +
        defectC G G' (compWeight L a₁) a₁ n θ Ψ f :=
  coupling_add_levelC_on hL ha₁ hn hp Finset.univ (fun _ _ _ _ => Finset.mem_univ _) θ Ψ f hθ

/-- The coupling on `S` reads the block field only on `S`. -/
theorem couplingCOn_congr_left (S : Finset (Torus d (N₀ * L ^ K))) (a₁ : ℝ) (p : ℕ)
    {θ₁ θ₂ : Torus d (N₀ * L ^ K) → Fin N → ℂ} (Ψ : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (h : ∀ x ∈ S, θ₁ x = θ₂ x) : couplingCOn S G' a₁ p θ₁ Ψ = couplingCOn S G' a₁ p θ₂ Ψ := by
  unfold couplingCOn
  congr 1
  exact Finset.sum_congr rfl fun x hx => by rw [h x hx]

/-- The level energy on `S` reads the field only on `S`. -/
theorem levelEnergyCOn_congr_left (S : Finset (Torus d (N₀ * L ^ K))) (a : ℕ → ℝ) (m : ℕ)
    {θ₁ θ₂ : Torus d (N₀ * L ^ K) → Fin N → ℂ} (f : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (h : ∀ x ∈ S, θ₁ x = θ₂ x) : levelEnergyCOn S G a m θ₁ f = levelEnergyCOn S G a m θ₂ f := by
  unfold levelEnergyCOn
  congr 1
  exact Finset.sum_congr rfl fun x hx => by rw [h x hx]

/-- The defect on a union `S` of `(n+1)`-blocks reads the block field only on `S`. -/
theorem defectCOn_congr_left (S : Finset (Torus d (N₀ * L ^ K)))
    (hS : ∀ z ∈ S, ∀ y ∈ G'.blk (n + 1) z, y ∈ S) (a : ℕ → ℝ) (a₁ : ℝ)
    {θ₁ θ₂ : Torus d (N₀ * L ^ K) → Fin N → ℂ} (Ψ f : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (h : ∀ x ∈ S, θ₁ x = θ₂ x) :
    defectCOn S G G' a a₁ n θ₁ Ψ f = defectCOn S G G' a a₁ n θ₂ Ψ f := by
  have hps : ∀ x ∈ S, ∀ i, psiStar G G' a n (n + 1) θ₁ f x i =
      psiStar G G' a n (n + 1) θ₂ f x i := fun x hx i => by
    unfold psiStar; rw [h x hx]
  have hbm : ∀ x ∈ S, ∀ i, blockMean G' (n + 1) (fun y => Ψ y i - psiStar G G' a n (n + 1) θ₁ f y i) x =
      blockMean G' (n + 1) (fun y => Ψ y i - psiStar G G' a n (n + 1) θ₂ f y i) x := fun x hx i => by
    unfold blockMean
    congr 1
    exact Finset.sum_congr rfl fun y hy => by
      show Ψ y i - psiStar G G' a n (n + 1) θ₁ f y i = Ψ y i - psiStar G G' a n (n + 1) θ₂ f y i
      rw [hps y (hS x hx y hy) i]
  unfold defectCOn
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => by rw [hps x hx i]
  · congr 1
    exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => by rw [hbm x hx i]


end Bilinear

end Balaban.Fluctuation
