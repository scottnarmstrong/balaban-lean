/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.ReflectionMetric
public import Balaban.Multiscale.CutCube
public import Balaban.Multiscale.PointwisePotential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Intertwining of the cut operator with the reflected uncut operator (NC3, Lemma R3)

Let `E v = v ∘ F` be the even extension of a field `v` on the torus to the doubled torus.  For
`x = F p` in the cube, with the cut `cubeCut G □`, the rows agree:

* `Balaban.cutLaplacian_mulVec_row`: the row of `-Δ_cut + ν` at `x`;
* `Balaban.Reflection.lap_intertwine`: `(-Δ + ν)(E v)(p) = (-Δ_cut + ν) v (F p)`;
* `Balaban.Reflection.avg_intertwine`: `(Q* a Q)^*(E v)(p) = (Q* a Q) v (F p)`;
* `Balaban.Reflection.operator_intertwine`: the Dirichlet operator of the reflected set intertwines
  with the cut operator of `G` on `Ω₁`.
-/

@[expose] public section

namespace Balaban

open Matrix Finset

section Row

variable {d ℓ : ℕ} [NeZero ℓ]

/-- The row of the cut Laplacian at `x`: the Laplacian row plus the contribution of the removed
bonds at `x`. -/
theorem cutLaplacian_mulVec_row (hℓ : 2 ≤ ℓ) (ν : ℝ) (cut : Finset (Torus d ℓ × Fin d))
    (v : Torus d ℓ → ℝ) (x : Torus d ℓ) :
    (cutLaplacian ν cut *ᵥ v) x = (latticeLaplacian d ℓ ν *ᵥ v) x +
      ∑ μ : Fin d, ((if (x, μ) ∈ cut then v (x + Pi.single μ 1) - v x else 0) +
        (if (x - Pi.single μ 1, μ) ∈ cut then v (x - Pi.single μ 1) - v x else 0)) := by
  classical
  have : Fact (1 < ℓ) := ⟨hℓ⟩
  have hne : ∀ μ : Fin d, (Pi.single μ 1 : Torus d ℓ) ≠ 0 := by
    intro μ h
    have := congrFun h μ
    simp at this
  have hbond : ∀ (b : Torus d ℓ × Fin d), (bondMatrix b *ᵥ v) x =
      (v (b.1 + Pi.single b.2 1) - v b.1) *
        ((if x = b.1 + Pi.single b.2 1 then 1 else 0) - (if x = b.1 then 1 else 0)) := by
    intro b
    unfold bondMatrix
    rw [Matrix.vecMulVec_mulVec, bondVec_dotProduct]
    simp [bondVec, Pi.single_apply]
    ring
  have hsum : ∑ b ∈ cut, (bondMatrix b *ᵥ v) x =
      ∑ μ : Fin d, ((if (x - Pi.single μ 1, μ) ∈ cut then v x - v (x - Pi.single μ 1) else 0) -
        (if (x, μ) ∈ cut then v (x + Pi.single μ 1) - v x else 0)) := by
    have h1 := Fintype.sum_prod_type' (f := fun (x' : Torus d ℓ) (μ : Fin d) =>
      if (x', μ) ∈ cut then (bondMatrix (x', μ) *ᵥ v) x else 0)
    simp only [Prod.mk.eta] at h1
    rw [show ∑ b ∈ cut, (bondMatrix b *ᵥ v) x =
        ∑ b : Torus d ℓ × Fin d, if b ∈ cut then (bondMatrix b *ᵥ v) x else 0 by
      rw [Finset.sum_ite_mem, Finset.univ_inter]]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_eq_add (x - Pi.single μ 1) x (by
      intro h; exact hne μ (by
        have := congrArg (fun z => x - z) h
        simp at this))]
    · simp only [hbond, sub_add_cancel, ↓reduceIte]
      have h2 : ¬ x = x - Pi.single μ 1 := fun h => hne μ (by
        have := congrArg (fun z => x - z) h
        simpa using this.symm)
      have h3 : ¬ x = x + Pi.single μ 1 := fun h => hne μ (by
        have := congrArg (fun z => z - x) h
        simpa using this.symm)
      simp only [h2, h3, ↓reduceIte]
      split_ifs <;> ring
    · intro y _ hy
      by_cases hc : (y, μ) ∈ cut
      · simp only [hc, ↓reduceIte, hbond]
        have h1 : ¬ x = y + Pi.single μ 1 := fun h => hy.1 (by rw [h]; simp)
        have h2 : ¬ x = y := fun h => hy.2 h.symm
        simp [h1, h2]
      · simp [hc]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  unfold cutLaplacian
  rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.sum_mulVec, Finset.sum_apply, hsum]
  have : ∀ μ : Fin d, ((if (x - Pi.single μ 1, μ) ∈ cut then v x - v (x - Pi.single μ 1) else 0) -
        (if (x, μ) ∈ cut then v (x + Pi.single μ 1) - v x else 0)) =
      -((if (x, μ) ∈ cut then v (x + Pi.single μ 1) - v x else 0) +
        (if (x - Pi.single μ 1, μ) ∈ cut then v (x - Pi.single μ 1) - v x else 0)) := by
    intro μ
    split_ifs <;> ring
  simp only [this, Finset.sum_neg_distrib]
  ring

end Row

end Balaban

namespace Balaban.Reflection

open Matrix Balaban Balaban.Multiscale Balaban.Localization

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {q s : ℕ} {c : Fin d → ℕ} [NeZero s]

omit [NeZero s] in
theorem two_le_side (h : FoldSetting G q s c) : 2 ≤ N₀ * L ^ k := by
  have := Nat.mul_pos h.s_pos (L_pow_pos L q)
  have := h.side
  omega

omit [NeZero s] in
/-- A bond leaving the cube upwards is cut. -/
theorem cut_up_iff (h : FoldSetting G q s c) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ cubeOf N₀ L k q s c) (μ : Fin d) :
    (x, μ) ∈ cubeCut G (cubeOf N₀ L k q s c) ↔ x + Pi.single μ 1 ∉ cubeOf N₀ L k q s c := by
  rw [mem_cubeCut]
  have := (h.collar x hx μ).1
  tauto

omit [NeZero s] in
/-- A bond entering the cube from below is cut. -/
theorem cut_dn_iff (h : FoldSetting G q s c) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ cubeOf N₀ L k q s c) (μ : Fin d) :
    (x - Pi.single μ 1, μ) ∈ cubeCut G (cubeOf N₀ L k q s c) ↔
      x - Pi.single μ 1 ∉ cubeOf N₀ L k q s c := by
  rw [mem_cubeCut, sub_add_cancel]
  have := (h.collar x hx μ).2
  tauto

theorem fold_nbr_sum (h : FoldSetting G q s c) {M : Type*} [AddCommMonoid M]
    (v : Torus d (N₀ * L ^ k) → M) (p : Torus d (2 * s * L ^ q)) (μ : Fin d) :
    v (foldTo N₀ L k q s c (p + Pi.single μ 1)) + v (foldTo N₀ L k q s c (p - Pi.single μ 1)) =
      v (stepUpT (cubeOf N₀ L k q s c) (foldTo N₀ L k q s c p) μ) +
        v (stepDnT (cubeOf N₀ L k q s c) (foldTo N₀ L k q s c p) μ) := by
  have hS : 0 < s * L ^ q := Nat.mul_pos h.s_pos (L_pow_pos L q)
  rcases foldMap_nbr (c := c) (ℓ := N₀ * L ^ k) (two_mul_side L q s) hS h.side p μ with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · change v (foldMap _ _ _ c _) + v (foldMap _ _ _ c _) = _
    rw [h1, h2]; rfl
  · change v (foldMap _ _ _ c _) + v (foldMap _ _ _ c _) = _
    rw [h1, h2, add_comm]; rfl

/-- **Lemma R3 (Laplacian part).** -/
theorem lap_intertwine (h : FoldSetting G q s c) (ν : ℝ) (v : Torus d (N₀ * L ^ k) → ℝ)
    (p : Torus d (2 * s * L ^ q)) :
    (latticeLaplacian d (2 * s * L ^ q) ν *ᵥ fun p' => v (foldTo N₀ L k q s c p')) p =
      (cutLaplacian ν (cubeCut G (cubeOf N₀ L k q s c)) *ᵥ v) (foldTo N₀ L k q s c p) := by
  classical
  set x := foldTo N₀ L k q s c p with hxdef
  have hx : x ∈ cubeOf N₀ L k q s c := foldTo_mem_cubeOf p
  rw [latticeLaplacian_mulVec, cutLaplacian_mulVec_row (two_le_side h), latticeLaplacian_mulVec]
  rw [add_assoc, add_comm ((ν : ℝ) * v x), ← add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hs := fold_nbr_sum h v p μ
  rw [← hxdef] at hs
  have hup : stepUpT (cubeOf N₀ L k q s c) x μ =
      if x + Pi.single μ 1 ∈ cubeOf N₀ L k q s c then x + Pi.single μ 1 else x := rfl
  have hdn : stepDnT (cubeOf N₀ L k q s c) x μ =
      if x - Pi.single μ 1 ∈ cubeOf N₀ L k q s c then x - Pi.single μ 1 else x := rfl
  have hc1 := cut_up_iff h hx μ
  have hc2 := cut_dn_iff h hx μ
  have e1 : v (foldTo N₀ L k q s c (p + Pi.single μ 1)) +
      v (foldTo N₀ L k q s c (p - Pi.single μ 1)) = _ := hs
  have : 2 * v x - v (foldTo N₀ L k q s c (p + Pi.single μ 1)) -
        v (foldTo N₀ L k q s c (p - Pi.single μ 1)) =
      2 * v x - (v (stepUpT (cubeOf N₀ L k q s c) x μ) +
        v (stepDnT (cubeOf N₀ L k q s c) x μ)) := by rw [← e1]; ring
  rw [this, hup, hdn]
  by_cases h1 : x + Pi.single μ 1 ∈ cubeOf N₀ L k q s c <;>
    by_cases h2 : x - Pi.single μ 1 ∈ cubeOf N₀ L k q s c <;>
    simp [h1, h2, hc1, hc2] <;> ring


/-! ### The block average -/

omit [NeZero s] in
/-- A layer is a union of blocks of its own scale. -/
theorem layer_of_jBlock_eq (G' : GeneratingSet d L N₀ k ϱ) {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G'.layer n)
    (hb : jBlock d L N₀ k n x' = jBlock d L N₀ k n x) : x' ∈ G'.layer n := by
  rw [GeneratingSet.mem_layer] at hx ⊢
  refine ⟨(G'.blockUnion n hn1 hnk x' x hb).2 hx.1, ?_⟩
  intro h'
  by_cases hlt : n < k
  · have hcell := sameCell_of_jBlock_eq hnk hb
    have hcell' : SameCell (L ^ (n + 1)) x' x :=
      SameCell.mono (pow_dvd_pow L (Nat.le_succ n)) hcell
    exact hx.2 ((G'.blockUnion (n + 1) (by omega) (by omega) x' x
      (jBlock_eq_of_sameCell hcell')).1 h')
  · have : n = k := le_antisymm hnk (not_lt.1 hlt)
    subst this
    simp [G'.top] at h'


omit [NeZero s] in
/-- The row of the averaging matrix at a point of the layer `n`: the average over its block. -/
theorem avg_row_formula (G' : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) {n : ℕ} (hn1 : 1 ≤ n)
    (hnk : n ≤ k) {p : Torus d (N₀ * L ^ k)} (hp : p ∈ G'.layer n) (ψ : Torus d (N₀ * L ^ k) → ℝ) :
    (avgMatrix G' a *ᵥ ψ) p = a n / ((L : ℝ) ^ n) ^ 2 * ((((L ^ n : ℕ) : ℝ) ^ d)⁻¹ *
      ∑ p' ∈ Finset.univ.filter (fun p' => jBlock d L N₀ k n p' = jBlock d L N₀ k n p), ψ p') := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [avgMatrix_apply_layer_block G' a hn1 hnk hp]
  by_cases hb : jBlock d L N₀ k n p' = jBlock d L N₀ k n p
  · have hl := layer_of_jBlock_eq G' hn1 hnk hp hb
    have hbp : blockProjMatrix d (N₀ * L ^ k) (L ^ n) (N₀ * L ^ (k - n)) p p' =
        (((L ^ n : ℕ) : ℝ) ^ d)⁻¹ := by
      have hb' : blockMap (L ^ n) (N₀ * L ^ (k - n)) p = blockMap (L ^ n) (N₀ * L ^ (k - n)) p' :=
        hb.symm
      unfold blockProjMatrix
      simp only [hb', ↓reduceIte]
    simp only [hb, hl, hbp, ↓reduceIte]
    ring
  · have hbp : blockProjMatrix d (N₀ * L ^ k) (L ^ n) (N₀ * L ^ (k - n)) p p' = 0 := by
      have hb' : ¬ blockMap (L ^ n) (N₀ * L ^ (k - n)) p = blockMap (L ^ n) (N₀ * L ^ (k - n)) p' :=
        fun h => hb h.symm
      unfold blockProjMatrix
      simp only [hb', ↓reduceIte]
    simp [hb, hbp]

/-- The fold maps the `n`-block of `p` bijectively onto the `n`-block of its image. -/
theorem image_fold_block (h : FoldSetting G q s c) {n : ℕ} (hnq : n ≤ q)
    (p : Torus d (2 * s * L ^ q)) :
    (Finset.univ.filter (fun p' : Torus d (2 * s * L ^ q) =>
        jBlock d L (2 * s) q n p' = jBlock d L (2 * s) q n p)).image (foldTo N₀ L k q s c) =
      Finset.univ.filter (fun x' : Torus d (N₀ * L ^ k) =>
        jBlock d L N₀ k n x' = jBlock d L N₀ k n (foldTo N₀ L k q s c p)) ∧
    Set.InjOn (foldTo N₀ L k q s c) ((Finset.univ.filter (fun p' : Torus d (2 * s * L ^ q) =>
        jBlock d L (2 * s) q n p' = jBlock d L (2 * s) q n p) :
          Finset (Torus d (2 * s * L ^ q))) : Set (Torus d (2 * s * L ^ q))) := by
  classical
  have hnk : n ≤ k := hnq.trans h.q_le
  set A := Finset.univ.filter (fun p' : Torus d (2 * s * L ^ q) =>
        jBlock d L (2 * s) q n p' = jBlock d L (2 * s) q n p) with hA
  set B := Finset.univ.filter (fun x' : Torus d (N₀ * L ^ k) =>
        jBlock d L N₀ k n x' = jBlock d L N₀ k n (foldTo N₀ L k q s c p)) with hB
  have hmap : ∀ p' ∈ A, foldTo N₀ L k q s c p' ∈ B := by
    intro p' hp'
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hp'
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
    exact foldTo_jBlock_eq h hnq hp'
  have hinj : Set.InjOn (foldTo N₀ L k q s c) (A : Set (Torus d (2 * s * L ^ q))) := by
    intro p1 hp1 p2 hp2 hF
    simp only [hA, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
    exact foldTo_injOn_jBlock h hnq (hp1.trans hp2.symm) hF
  have hcardA : A.card = (L ^ n) ^ d := by
    have e : A = blockFibre (L ^ n) (2 * s * L ^ (q - n)) (jBlock d L (2 * s) q n p) := by
      ext x; rw [hA, Finset.mem_filter, mem_blockFibre]; simp [jBlock]
    rw [e]
    exact card_blockFibre (d := d) (ℓ := 2 * s * L ^ q) (N := L ^ n) (m := 2 * s * L ^ (q - n))
      (side_eq (N₀ := 2 * s) (k := q) (j := n) hnq) _
  have hcardB : B.card = (L ^ n) ^ d := by
    have e : B = blockFibre (L ^ n) (N₀ * L ^ (k - n))
        (jBlock d L N₀ k n (foldTo N₀ L k q s c p)) := by
      ext x; rw [hB, Finset.mem_filter, mem_blockFibre]; simp [jBlock]
    rw [e]
    exact card_blockFibre (d := d) (ℓ := N₀ * L ^ k) (N := L ^ n) (m := N₀ * L ^ (k - n))
      (side_eq (N₀ := N₀) (k := k) (j := n) hnk) _
  refine ⟨?_, hinj⟩
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hx
    exact hmap p' hp'
  · rw [Finset.card_image_of_injOn hinj, hcardA, hcardB]

theorem sum_fold_block (h : FoldSetting G q s c) {n : ℕ} (hnq : n ≤ q)
    {M : Type*} [AddCommMonoid M] (g : Torus d (N₀ * L ^ k) → M) (p : Torus d (2 * s * L ^ q)) :
    ∑ p' ∈ Finset.univ.filter (fun p' : Torus d (2 * s * L ^ q) =>
        jBlock d L (2 * s) q n p' = jBlock d L (2 * s) q n p), g (foldTo N₀ L k q s c p') =
      ∑ x' ∈ Finset.univ.filter (fun x' : Torus d (N₀ * L ^ k) =>
        jBlock d L N₀ k n x' = jBlock d L N₀ k n (foldTo N₀ L k q s c p)), g x' := by
  classical
  obtain ⟨himg, hinj⟩ := image_fold_block h hnq p
  rw [← himg, Finset.sum_image hinj]

/-- **Lemma R3 (averaging part).** -/
theorem avg_intertwine (h : FoldSetting G q s c) (a : ℕ → ℝ) (v : Torus d (N₀ * L ^ k) → ℝ)
    (p : Torus d (2 * s * L ^ q)) :
    (avgMatrix (reflectedGS G h) a *ᵥ fun p' => v (foldTo N₀ L k q s c p')) p =
      (avgMatrix G a *ᵥ v) (foldTo N₀ L k q s c p) := by
  obtain ⟨hn1, hnq, hpl⟩ := (reflectedGS G h).layerIndex_spec (mem_reflectedGS_Ω_one h p)
  set n := (reflectedGS G h).layerIndex p with hn
  have hnk : n ≤ k := hnq.trans h.q_le
  have hFl : foldTo N₀ L k q s c p ∈ G.layer n := (mem_layer_reflectedGS_iff h hnq p).1 hpl
  rw [avg_row_formula (reflectedGS G h) a hn1 hnq hpl, avg_row_formula G a hn1 hnk hFl,
    sum_fold_block h hnq v p]


/-- **Lemma R3 (full matrix).** -/
theorem fullMatrix_intertwine (h : FoldSetting G q s c) (a : ℕ → ℝ) (ν : ℝ)
    (ψ : Torus d (N₀ * L ^ k) → ℂ) (p : Torus d (2 * s * L ^ q)) :
    ((fullMatrix (reflectedGS G h) a ν).map (algebraMap ℝ ℂ) *ᵥ
        fun p' => ψ (foldTo N₀ L k q s c p')) p =
      ((cutFullMatrix G a ν (cubeCut G (cubeOf N₀ L k q s c))).map (algebraMap ℝ ℂ) *ᵥ ψ)
        (foldTo N₀ L k q s c p) := by
  apply Complex.ext
  · rw [re_mulVec_map, re_mulVec_map]
    unfold fullMatrix cutFullMatrix
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Pi.add_apply, Pi.add_apply,
      lap_intertwine h ν (fun x => (ψ x).re) p, avg_intertwine h a (fun x => (ψ x).re) p]
  · rw [im_mulVec_map, im_mulVec_map]
    unfold fullMatrix cutFullMatrix
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Pi.add_apply, Pi.add_apply,
      lap_intertwine h ν (fun x => (ψ x).im) p, avg_intertwine h a (fun x => (ψ x).im) p]

/-- The even extension `E u = u ∘ F` of a field on `Ω₁` to the doubled torus. -/
def reflU (h : FoldSetting G q s c) (u : G.Ω 1 → ℂ) : (reflectedGS G h).Ω 1 → ℂ :=
  fun p => u ⟨foldTo N₀ L k q s c p, foldTo_mem_Ω_one h p⟩

/-- The reflected diagonal perturbation `A* = A ∘ F`. -/
def reflAlpha (h : FoldSetting G q s c) (α : G.Ω 1 → ℂ) : (reflectedGS G h).Ω 1 → ℂ :=
  reflU h α

theorem zeroExt_reflU (h : FoldSetting G q s c) (u : G.Ω 1 → ℂ) (p : Torus d (2 * s * L ^ q)) :
    zeroExt ((reflectedGS G h).Ω 1) (reflU h u) p = zeroExt (G.Ω 1) u (foldTo N₀ L k q s c p) := by
  have h1 := mem_reflectedGS_Ω_one h p
  have h2 := foldTo_mem_Ω_one h p
  simp [zeroExt, h1, h2, reflU]

/-- **Lemma R3 (operator intertwining).** On even functions the uncut operator of the reflected
set is the cube restriction of the cut operator: `H*_D (E u) = E (H_cut u)`. -/
theorem operator_intertwine (h : FoldSetting G q s c) (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (u : G.Ω 1 → ℂ) (p : (reflectedGS G h).Ω 1) :
    (dirichletOperator (reflectedGS G h) a ν (reflAlpha h α) *ᵥ reflU h u) p =
      (cutOperator G a ν (cubeCut G (cubeOf N₀ L k q s c)) α *ᵥ u)
        ⟨foldTo N₀ L k q s c p, foldTo_mem_Ω_one h p⟩ := by
  rw [← cutOperator_empty]
  have h1 := cutOperator_eq (reflectedGS G h) (u := reflU h u)
    (f := cutOperator (reflectedGS G h) a ν ∅ (reflAlpha h α) *ᵥ reflU h u) rfl p
  have h2 := cutOperator_eq G (u := u)
    (f := cutOperator G a ν (cubeCut G (cubeOf N₀ L k q s c)) α *ᵥ u) rfl
    ⟨foldTo N₀ L k q s c p, foldTo_mem_Ω_one h p⟩
  rw [← h1, ← h2]
  have hz : zeroExt ((reflectedGS G h).Ω 1) (reflU h u) =
      fun p' => zeroExt (G.Ω 1) u (foldTo N₀ L k q s c p') := funext (zeroExt_reflU h u)
  rw [hz, cutFullMatrix_empty, fullMatrix_intertwine h a ν (zeroExt (G.Ω 1) u) p]
  rfl

end Balaban.Reflection
