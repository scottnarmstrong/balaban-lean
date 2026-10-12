/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CubeActionRealStar
public import Balaban.LargeField.Operators.MainAction
import Balaban.Multiscale.ConstraintKernel
import Balaban.Multiscale.ConstraintComm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The star cube action is the real localized action (FLUCTUATION.md §4.2, LFR Definition II.5.4)

For real data `(φ, ψ, h)` (the field `φ̄` on the sites, the multiscale field `ψ_n` on the
`n`-blocks, the external direction `h`) and the complex image `(D, toFieldC G φ)`:

* `cubeBlock_sum_eq`, `cubeMass_sum_eq`, `cubeBond_sum_eq`: the block, mass and bond parts of
  `cubeActionStar G a ν X` are the corresponding parts of `actionG` (the block term of `actionG`
  sums over the `n`-blocks meeting `Λ_n ∩ X`, the site sum over `X ∩ Λ_n`: `X` is a union of the
  blocks of each layer) and `½ bondE X φ + ¼ starBondE X φ` (bonds inside `X` count `½`, the
  star bonds `¼`: the bond-charging of `starWeight`);
* `cubeActionStar_eq_actionG`: **`A_X(D; φ) = A_G(X; ψ, φ) + ¼ ∑_{b ∈ st(X)} |∂φ|²`**, the
  bracket of `mainActionLoc` (Definition II.5.4) for a common generating set `G`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Finset

section Real

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L N₀ k ϱ)

/-- The real field `φ`, as a complex field on `Ω₁`. -/
noncomputable def toFieldC (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin N)) :
    G.Ω 1 × Fin N → ℂ := fun p => ((φ p.1 p.2 : ℝ) : ℂ)

variable {G}

theorem sum_sq_complex (v : EuclideanSpace ℝ (Fin N)) :
    ∑ i, ((v i : ℝ) : ℂ) * ((v i : ℝ) : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]; push_cast; ring

theorem svec_toFieldC (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin N)) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.Ω 1) (i : Fin N) : svec G (toFieldC G φ) y i = ((φ y i : ℝ) : ℂ) := by
  rw [svec_of_mem G _ ⟨y, hy⟩ i]; rfl

/-- The block average of the complex image is the complex image of the real block average. -/
theorem blockAvg_toFieldC (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin N)) {n : ℕ} (hn1 : 1 ≤ n)
    (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) (i : Fin N) :
    blockAvg G (toFieldC G φ) x i =
      ((bavgL d L N₀ k n φ (blkMap d L N₀ k n x) i : ℝ) : ℂ) := by
  have hli : G.layerIndex x = n := G.layerIndex_eq hn1 hnk hx
  have hsub := blk_subset_Ω G hn1 hnk hx
  unfold blockAvg
  rw [hli]
  have e1 : ∑ y ∈ G.blk n x, svec G (toFieldC G φ) y i = ((∑ y ∈ G.blk n x, φ y i : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun y hy => svec_toFieldC φ (hsub hy) i
  rw [e1]
  unfold bavgL bavg
  have e2 : blkMap d L N₀ k n x = jBlock d L N₀ k n x := rfl
  rw [e2, ← blk_eq_fibre G n x]
  simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
  push_cast
  rfl

variable {a : ℕ → ℝ}

/-- The block part of the star action of `X` is the block part of `actionG`. -/
theorem cubeBlock_sum_eq (hd : 2 ≤ d) (X : Finset (Site d L N₀ k)) (hXΩ : X ⊆ G.Ω 1)
    (hXblk : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ X, x ∈ G.layer n → ∀ y ∈ G.blk n x, y ∈ X)
    (D : BgData G N) (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin N))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin N))
    (hΨ : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ G.layer n, ∀ i,
      D.Ψ x i = ((ψ n (blkMap d L N₀ k n x) i : ℝ) : ℂ)) :
    ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ X then
        cubeBlockTerm G a D.Ψ (toFieldC G φ) x else 0) =
      ((∑ n ∈ Finset.Icc 1 k, ∑ y ∈ tBlocks d L N₀ k n (lam G n ∩ X),
        a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ k n φ y‖ ^ 2 : ℝ) : ℂ) := by
  classical
  set R' : ℕ → Torus d (N₀ * L ^ k) → ℝ := fun n x =>
    a n / ((L : ℝ) ^ n) ^ 2 * ‖ψ n (blkMap d L N₀ k n x) - bavgL d L N₀ k n φ (blkMap d L N₀ k n x)‖ ^ 2
    with hR'
  -- Step 1: sum over the subtype becomes a sum over `X`
  have step1 : ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ X then
        cubeBlockTerm G a D.Ψ (toFieldC G φ) x else 0) =
      ∑ x ∈ X, ((R' (G.layerIndex x) x : ℝ) : ℂ) := by
    have h1 : ∀ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ X then
        cubeBlockTerm G a D.Ψ (toFieldC G φ) x else 0) =
        (if (x : Torus d (N₀ * L ^ k)) ∈ X then ((R' (G.layerIndex x) x : ℝ) : ℂ) else 0) := by
      intro x
      by_cases hx : (x : Torus d (N₀ * L ^ k)) ∈ X
      · simp only [hx, ↓reduceIte]
        obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec x.2
        unfold cubeBlockTerm
        set n := G.layerIndex (x : Torus d (N₀ * L ^ k)) with hn
        have e1 : ∀ i, D.Ψ x i - blockAvg G (toFieldC G φ) x i =
            ((ψ n (blkMap d L N₀ k n x) - bavgL d L N₀ k n φ (blkMap d L N₀ k n x) : EuclideanSpace ℝ (Fin N)) i : ℝ) := by
          intro i
          rw [hΨ n hn1 hnk x hxl i, blockAvg_toFieldC φ hn1 hnk hxl i]
          rw [← Complex.ofReal_sub]
          rfl
        simp only [e1]
        rw [sum_sq_complex]
        simp only [hR']
        push_cast
        ring
      · simp [hx]
    rw [Finset.sum_congr rfl fun x _ => h1 x]
    have := Finset.sum_coe_sort (G.Ω 1)
      (fun x => if x ∈ X then ((R' (G.layerIndex x) x : ℝ) : ℂ) else 0)
    rw [this, Finset.sum_ite_mem, Finset.inter_eq_right.2 hXΩ]
  rw [step1, ← Complex.ofReal_sum]
  congr 1
  -- Step 3: split by layers
  rw [← Finset.sum_fiberwise_of_maps_to (s := X) (t := Finset.Icc 1 k) (g := G.layerIndex)
    (fun x hx => by
      obtain ⟨h1, h2, -⟩ := G.layerIndex_spec (hXΩ hx)
      exact Finset.mem_Icc.2 ⟨h1, h2⟩)]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hnk⟩ := Finset.mem_Icc.1 hn
  have hlam : lam G n = G.layer n := by unfold lam; simp; omega
  have hS : X.filter (fun x => G.layerIndex x = n) = G.layer n ∩ X := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hx, rfl⟩
      exact ⟨(G.layerIndex_spec (hXΩ hx)).2.2, hx⟩
    · rintro ⟨hxl, hx⟩
      exact ⟨hx, G.layerIndex_eq hn1 hnk hxl⟩
  rw [hlam, Finset.sum_congr rfl fun x hx => by
    rw [(Finset.mem_filter.1 hx).2], hS]
  set S := G.layer n ∩ X with hSdef
  have hmap : ∀ x ∈ S, blkMap d L N₀ k n x ∈ tBlocks d L N₀ k n S := fun x hx =>
    Finset.mem_image_of_mem _ hx
  rw [← Finset.sum_fiberwise_of_maps_to (g := blkMap d L N₀ k n) hmap]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hy
  have hfib : S.filter (fun x => blkMap d L N₀ k n x = blkMap d L N₀ k n x₀) =
      blockFibre (L ^ n) (N₀ * L ^ (k - n)) (blkMap d L N₀ k n x₀) := by
    ext z
    simp only [Finset.mem_filter, mem_blockFibre, hSdef, Finset.mem_inter]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h
      have hb : jBlock d L N₀ k n z = jBlock d L N₀ k n x₀ := h
      have hx₀S := Finset.mem_inter.1 hx₀
      refine ⟨⟨(G.mem_layer_iff hn1 hnk hb).2 hx₀S.1, ?_⟩, h⟩
      exact hXblk n hn1 hnk x₀ hx₀S.2 hx₀S.1 z (G.mem_blk.2 hb)
  have hconst : ∀ x ∈ S.filter (fun x => blkMap d L N₀ k n x = blkMap d L N₀ k n x₀),
      R' n x = R' n x₀ := by
    intro x hx
    simp only [hR']
    rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, hfib,
    card_blockFibre (side_eq hnk)]
  simp only [hR', nsmul_eq_mul]
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hdd : n * d = n * (d - 2) + 2 * n := by
    have : d = (d - 2) + 2 := by omega
    conv_lhs => rw [this]
    ring
  push_cast
  rw [← pow_mul, hdd, pow_add]
  field_simp
  ring

/-- The mass part of the star action of `X` is the mass part of `actionG`. -/
theorem cubeMass_sum_eq (X : Finset (Site d L N₀ k)) (hXΩ : X ⊆ G.Ω 1) (D : BgData G N)
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (hh : ∀ x ∈ X, ∀ i, D.h x i = ((hv i : ℝ) : ℂ)) :
    ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ X then
        cubeMassTerm G D.h (toFieldC G φ) x else 0) =
      ((∑ x ∈ X, ‖φ x - hv‖ ^ 2 : ℝ) : ℂ) := by
  classical
  have h1 : ∀ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ X then
      cubeMassTerm G D.h (toFieldC G φ) x else 0) =
      (if (x : Torus d (N₀ * L ^ k)) ∈ X then ((‖φ x - hv‖ ^ 2 : ℝ) : ℂ) else 0) := by
    intro x
    by_cases hx : (x : Torus d (N₀ * L ^ k)) ∈ X
    · simp only [hx, ↓reduceIte]
      unfold cubeMassTerm
      have e1 : ∀ i, toFieldC G φ (x, i) - D.h x i = (((φ x - hv : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) := by
        intro i
        rw [hh x hx i]
        show ((φ x i : ℝ) : ℂ) - ((hv i : ℝ) : ℂ) = _
        rw [← Complex.ofReal_sub]
        rfl
      simp only [e1]
      exact sum_sq_complex _
    · simp [hx]
  rw [Finset.sum_congr rfl fun x _ => h1 x]
  have := Finset.sum_coe_sort (G.Ω 1)
    (fun x => if x ∈ X then ((‖φ x - hv‖ ^ 2 : ℝ) : ℂ) else 0)
  rw [this, Finset.sum_ite_mem, Finset.inter_eq_right.2 hXΩ, Complex.ofReal_sum]

theorem barField_toFieldC (D : BgData G N) (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin N))
    (hout : ∀ x, x ∉ G.Ω 1 → ∀ i, D.Ψ x i = ((φ x i : ℝ) : ℂ)) (x : Torus d (N₀ * L ^ k))
    (i : Fin N) : barField G D.Ψ (toFieldC G φ) x i = ((φ x i : ℝ) : ℂ) := by
  by_cases hx : x ∈ G.Ω 1
  · simp [barField, hx, toFieldC]
  · simp [barField, hx, hout x hx i]

/-- The bond part of the star action of `X` is `½ bondE + ¼ starBondE`. -/
theorem cubeBond_sum_eq (X : Finset (Site d L N₀ k)) (hXΩ : X ⊆ G.Ω 1) (D : BgData G N)
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin N))
    (hout : ∀ x, x ∉ G.Ω 1 → ∀ i, D.Ψ x i = ((φ x i : ℝ) : ℂ)) :
    ∑ x : Torus d (N₀ * L ^ k), cubeBondStar G X D.Ψ (toFieldC G φ) x =
      ((bondE X φ + 1 / 2 * starBondE X φ : ℝ) : ℂ) := by
  classical
  have hbt : ∀ x μ, ∑ i, (barField G D.Ψ (toFieldC G φ) (x + Pi.single μ 1) i -
        barField G D.Ψ (toFieldC G φ) x i) *
      (barField G D.Ψ (toFieldC G φ) (x + Pi.single μ 1) i -
        barField G D.Ψ (toFieldC G φ) x i) = ((bondTerm φ μ x : ℝ) : ℂ) := by
    intro x μ
    unfold bondTerm
    have e1 : ∀ i, barField G D.Ψ (toFieldC G φ) (x + Pi.single μ 1) i -
        barField G D.Ψ (toFieldC G φ) x i =
        (((φ (x + Pi.single μ 1) - φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) := by
      intro i
      rw [barField_toFieldC D φ hout, barField_toFieldC D φ hout, ← Complex.ofReal_sub]
      rfl
    simp only [e1]
    exact sum_sq_complex _
  unfold bondE bondEdir starBondE
  push_cast
  unfold cubeBondStar
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold starWeight
  rw [hbt x μ]
  by_cases h1 : x ∈ X <;> by_cases h2 : x + Pi.single μ 1 ∈ X
  · have : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 := Or.inl (hXΩ h1)
    simp [h1, h2, this]
  · have : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 := Or.inl (hXΩ h1)
    simp [h1, h2, this]
  · have : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 := Or.inr (hXΩ h2)
    simp [h1, h2, this]
  · simp [h1, h2]

/-- **The star cube action of `X` is the localized real action.**  For real data `(φ, ψ, h)` and
their complex image (`D`, `toFieldC G φ`) with the same generating set `G`,
`A_Q(X; D, φ) = A_G(X; ψ, φ) + ¼ ∑_{b ∈ st(X)} |∂φ|²`, where `φ` is the extension of the
background by the data outside `Ω₁`, `ψ_n` is the value of `Ψ` on the `n`-blocks of layer `n`, `h`
the (constant) external direction on `X ⊆ Ω₁`, and `X` is a union of the blocks of each layer. -/
theorem cubeActionStar_eq_actionG (hd : 2 ≤ d) (X : Finset (Site d L N₀ k)) (hXΩ : X ⊆ G.Ω 1)
    (hXblk : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ X, x ∈ G.layer n → ∀ y ∈ G.blk n x, y ∈ X)
    (ν : ℝ) (D : BgData G N) (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin N))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (hout : ∀ x, x ∉ G.Ω 1 → ∀ i, D.Ψ x i = ((φ x i : ℝ) : ℂ))
    (hΨ : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ G.layer n, ∀ i,
      D.Ψ x i = ((ψ n (blkMap d L N₀ k n x) i : ℝ) : ℂ))
    (hh : ∀ x ∈ X, ∀ i, D.h x i = ((hv i : ℝ) : ℂ)) :
    cubeActionStar G a ν X D.Ψ D.h (toFieldC G φ) =
      ((actionG G a ν hv X ψ φ + 1 / 4 * starBondE X φ : ℝ) : ℂ) := by
  have hb := cubeBlock_sum_eq (a := a) hd X hXΩ hXblk D φ ψ hΨ
  have hm := cubeMass_sum_eq X hXΩ D φ hv hh
  have hbo := cubeBond_sum_eq X hXΩ D φ hout
  unfold cubeActionStar
  rw [hb, hm, hbo]
  unfold actionG
  push_cast
  ring

end Real
end Balaban.Fluctuation
