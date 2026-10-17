/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.IrrelTorusDefectPointSymm
public import Balaban.SmallField.IrrelTorusDefectRawLimit

/-!
# Reindexing a raw pair sum under a point symmetry

The finite Hessian has the point symmetries proved in `IrrelTorusDefectPointSymm`. This
algebraic reindexing is shared by coordinate reflection and exchange.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.Localization.DecEquiv

/-- Reindex a finite pair sum by an involution preserving its index set and Hessian kernel. -/
theorem weighted_double_sum_invol {α : Type*} [DecidableEq α]
    (S : Finset α) (r : α → α) (H w : α → α → ℂ)
    (hinv : ∀ x, r (r x) = x) (hS : ∀ x ∈ S, r x ∈ S)
    (hH : ∀ u ∈ S, ∀ v ∈ S, H (r u) (r v) = H u v) :
    (∑ u ∈ S, ∑ v ∈ S, H u v * w u v) =
      ∑ u ∈ S, ∑ v ∈ S, H u v * w (r u) (r v) := by
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => (r p.1, r p.2)) (fun p => (r p.1, r p.2))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product] at hp ⊢
    exact ⟨hS p.1 hp.1, hS p.2 hp.2⟩
  · intro p hp
    rw [Finset.mem_product] at hp ⊢
    exact ⟨hS p.1 hp.1, hS p.2 hp.2⟩
  · intro p hp
    ext <;> simp [hinv]
  · intro p hp
    ext <;> simp [hinv]
  · intro p hp
    rw [Finset.mem_product] at hp
    simp only [hinv, hH p.1 hp.1 p.2 hp.2]

/-- The signed shortest representative is odd after assigning zero to the antipodal tie.
This convention is needed for an exact reflection identity on even tori. -/
theorem corrected_valMinAbs_neg {n : ℕ} [NeZero n] (x : ZMod n) :
    (if 2 * (-x).val = n then (0 : ℤ) else (-x).valMinAbs) =
      -(if 2 * x.val = n then (0 : ℤ) else x.valMinAbs) := by
  by_cases ht : 2 * x.val = n
  · have heq : -x = x := x.neg_eq_self_iff.2 (Or.inr ht)
    simp only [heq, ht, ↓reduceIte, neg_zero]
  · have htneg : 2 * (-x).val ≠ n := by
      intro hn
      have heq : -x = x := by
        have h := ((-x).neg_eq_self_iff).2 (Or.inr hn)
        simpa only [neg_neg] using h.symm
      rw [heq] at hn
      exact ht hn
    simp only [ht, htneg, ↓reduceIte]
    exact ZMod.valMinAbs_neg_of_ne_half ht

/-- The antipodal correction does not enlarge a shortest representative. -/
theorem abs_corrected_valMinAbs_le {n : ℕ} [NeZero n] (w : ℤ) :
    |if 2 * (((w : ℤ) : ZMod n)).val = n then (0 : ℤ)
      else (((w : ℤ) : ZMod n)).valMinAbs| ≤ |w| := by
  split_ifs
  · simp
  · exact abs_valMinAbs_le n w

/-- On a displacement shorter than half the side, the corrected representative is the
integer displacement itself. -/
theorem corrected_valMinAbs_intCast_of_small {n : ℕ} [NeZero n] {w : ℤ}
    (hw : 2 * |w| < n) :
    (if 2 * (((w : ℤ) : ZMod n)).val = n then (0 : ℤ)
      else (((w : ℤ) : ZMod n)).valMinAbs) = w := by
  have hv := valMinAbs_intCast_of_small hw
  have ht : 2 * (((w : ℤ) : ZMod n)).val ≠ n := by
    intro h
    have hh := (ZMod.valMinAbs_mul_two_eq_iff _).2 h
    rw [hv] at hh
    have habs := le_abs_self w
    omega
  simp only [ht, ↓reduceIte, hv]

/-- The corrected torus coordinate agrees with the integer block displacement while the
pair fits inside half the side. -/
theorem corrected_ibase_sub_of_small {d L N₁ m₁ k j : ℕ} [NeZero L] [NeZero N₁]
    (hjk : j ≤ k) (z z' : Site d) (μ : Fin d)
    (hsmall : 2 * |z μ - z' μ| < ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ)) :
    ((if 2 * ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z -
        ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z') μ).val =
          N₁ * L ^ m₁ * L ^ k then (0 : ℤ)
       else ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z -
        ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z') μ).valMinAbs) : ℂ) /
        ((L : ℂ) ^ j) = ((z μ - z' μ : ℤ) : ℂ) := by
  have hside : ((N₁ * L ^ m₁ * L ^ k : ℕ) : ℤ) =
      ((L ^ j : ℕ) : ℤ) * ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
    exact_mod_cast side_eq hjk
  have hp : (0 : ℤ) < ((L ^ j : ℕ) : ℤ) := by exact_mod_cast pow_pos (NeZero.pos L) j
  have heq : (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z -
      ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z') μ =
      ((((L ^ j : ℕ) : ℤ) * (z μ - z' μ) : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ k)) := by
    simp only [ibase, Pi.sub_apply]; push_cast; ring
  have hsmall' : 2 * |((L ^ j : ℕ) : ℤ) * (z μ - z' μ)| <
      ((N₁ * L ^ m₁ * L ^ k : ℕ) : ℤ) := by
    rw [abs_mul, abs_of_pos hp, hside]
    nlinarith
  rw [heq]
  have hcorr := corrected_valMinAbs_intCast_of_small hsmall'
  have hcorrC := congrArg (fun t : ℤ => (t : ℂ)) hcorr
  simp only [Int.cast_ite, Int.cast_zero] at hcorrC
  simp only [Int.cast_zero]
  rw [hcorrC]
  push_cast
  have hL : ((L : ℂ) ^ j) ≠ 0 := by exact_mod_cast (pow_ne_zero j (NeZero.ne L))
  field_simp

/-- The corrected coordinate difference is bounded by the integer displacement, even
for a shape which does not fit in the centred chart. -/
theorem norm_corrected_ibase_sub_le {d L N₁ m₁ k j : ℕ} [NeZero L] [NeZero N₁]
    (z z' : Site d) (μ : Fin d) :
    ‖((if 2 * ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z -
        ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z') μ).val =
          N₁ * L ^ m₁ * L ^ k then (0 : ℤ)
       else ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z -
        ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z') μ).valMinAbs) : ℂ) /
        ((L : ℂ) ^ j)‖ ≤ |(((z μ - z' μ : ℤ) : ℝ))| := by
  have heq : (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z -
      ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z') μ =
      ((((L ^ j : ℕ) : ℤ) * (z μ - z' μ) : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ k)) := by
    simp only [ibase, Pi.sub_apply]; push_cast; ring
  rw [heq]
  have habs := abs_corrected_valMinAbs_le (n := N₁ * L ^ m₁ * L ^ k)
    (((L ^ j : ℕ) : ℤ) * (z μ - z' μ))
  have habsR : |((if 2 * (((((L ^ j : ℕ) : ℤ) * (z μ - z' μ) : ℤ) :
      ZMod (N₁ * L ^ m₁ * L ^ k))).val =
      N₁ * L ^ m₁ * L ^ k then (0 : ℤ)
      else (((((L ^ j : ℕ) : ℤ) * (z μ - z' μ) : ℤ) :
        ZMod (N₁ * L ^ m₁ * L ^ k))).valMinAbs) : ℝ)| ≤
      |((((L ^ j : ℕ) : ℤ) * (z μ - z' μ) : ℤ) : ℝ)| := by
    exact_mod_cast habs
  have hLpos : (0 : ℝ) < (L : ℝ) ^ j := by
    exact_mod_cast pow_pos (NeZero.pos L) j
  rw [norm_div, norm_pow, Complex.norm_natCast]
  by_cases ht : 2 * (((((L ^ j : ℕ) : ℤ) * (z μ - z' μ) : ℤ) :
      ZMod (N₁ * L ^ m₁ * L ^ k))).val = N₁ * L ^ m₁ * L ^ k
  · simp only [ht, ↓reduceIte]
    simp
  · simp only [ht, ↓reduceIte, Complex.norm_intCast]
    simp only [ht, ↓reduceIte] at habsR
    push_cast at habsR
    rw [abs_mul, abs_of_pos hLpos] at habsR
    push_cast
    exact (div_le_iff₀ hLpos).2 (by nlinarith)

/-- The corrected finite-volume matrix weight satisfies the common squared-length bound. -/
theorem norm_corrected_pair_le_sq {d L N₁ m₁ k j : ℕ} [NeZero L] [NeZero N₁]
    (z z' : Site d) (μ η : Fin d) :
    let q : ZMod (N₁ * L ^ m₁ * L ^ k) → ℂ :=
      fun x => ((if 2 * x.val = N₁ * L ^ m₁ * L ^ k then (0 : ℤ)
        else x.valMinAbs) : ℂ) / ((L : ℂ) ^ j)
    ‖q ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z -
        ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z') μ) *
      q ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z -
        ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z') η)‖ ≤
      ∑ ξ, (((z ξ - z' ξ : ℤ) : ℝ)) ^ 2 := by
  dsimp only
  rw [norm_mul]
  have hμ := norm_corrected_ibase_sub_le (L := L) (N₁ := N₁)
    (m₁ := m₁) (k := k) (j := j) z z' μ
  have hη := norm_corrected_ibase_sub_le (L := L) (N₁ := N₁)
    (m₁ := m₁) (k := k) (j := j) z z' η
  have hprod : _ ≤ |(((z μ - z' μ : ℤ) : ℝ))| *
      |(((z η - z' η : ℤ) : ℝ))| :=
    mul_le_mul hμ hη (norm_nonneg _) (abs_nonneg _)
  calc
    _ ≤ |(((z μ - z' μ : ℤ) : ℝ))| * |(((z η - z' η : ℤ) : ℝ))| := hprod
    _ = ‖(((z μ - z' μ : ℤ) : ℂ) * (((z η - z' η : ℤ) : ℂ)))‖ := by
      rw [norm_mul, Complex.norm_intCast, Complex.norm_intCast]
    _ ≤ ∑ ξ, (((z ξ - z' ξ : ℤ) : ℝ)) ^ 2 :=
      norm_pair_coord_mul_le_sq z z' μ η

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {P : Consts}
  {β ν a : ℕ → ℝ} {Ek : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ} {j : ℕ} {ρ : ℝ}

omit [NeZero L] [NeZero N₁] in
/-- Coordinate exchange preserves the level lattice of aligned sites. -/
theorem aligned_swapJ (μ η : Fin d) {x : CTorus d L N₁ m₁ k}
    (hx : Aligned (L ^ j) x) : Aligned (L ^ j) (swapJ μ η x) := by
  intro ξ
  change (x ((Equiv.swap μ η) ξ)).val % L ^ j = 0
  exact hx _

omit [NeZero L] [NeZero N₁] in
/-- A centred coordinate exchange permutes the coordinate differences of a pair. -/
theorem swapJ_sub_at_apply (μ η ξ : Fin d)
    (y u v : CTorus d L N₁ m₁ k) :
    ((swapJ μ η (u - y) + y) - (swapJ μ η (v - y) + y)) ξ =
      (u - v) ((Equiv.swap μ η) ξ) := by
  simp only [Pi.sub_apply, Pi.add_apply]
  change (u ((Equiv.swap μ η) ξ) - y ((Equiv.swap μ η) ξ) + y ξ) -
      (v ((Equiv.swap μ η) ξ) - y ((Equiv.swap μ η) ξ) + y ξ) =
        u ((Equiv.swap μ η) ξ) - v ((Equiv.swap μ η) ξ)
  abel

omit [NeZero L] [NeZero N₁] in
/-- Reflection of a pair negates the reflected coordinate difference. -/
theorem reflBase_sub_at_same (μ : Fin d)
    (y u v : CTorus d L N₁ m₁ k) :
    ((reflBase (L ^ j) μ (L ^ j : ZMod _) (u - y) + y) -
      (reflBase (L ^ j) μ (L ^ j : ZMod _) (v - y) + y)) μ =
      -((u - v) μ) := by
  simp only [Pi.sub_apply, Pi.add_apply]
  simp only [reflBase, Function.update_self]
  simp only [Pi.sub_apply]
  abel

omit [NeZero L] [NeZero N₁] in
/-- Reflection leaves every other coordinate difference fixed. -/
theorem reflBase_sub_at_other (μ ξ : Fin d) (h : ξ ≠ μ)
    (y u v : CTorus d L N₁ m₁ k) :
    ((reflBase (L ^ j) μ (L ^ j : ZMod _) (u - y) + y) -
      (reflBase (L ^ j) μ (L ^ j : ZMod _) (v - y) + y)) ξ =
      (u - v) ξ := by
  simp only [Pi.sub_apply, Pi.add_apply]
  simp only [reflBase, Function.update_of_ne h]
  simp only [Pi.sub_apply]
  abel

omit [NeZero L] [NeZero N₁] in
/-- An odd coordinate weight changes sign under reflection in exactly one of its axes. -/
theorem pair_coord_weight_flip_at (q : ZMod (N₁ * L ^ m₁ * L ^ k) → ℂ)
    (hq : ∀ x, q (-x) = -q x) (μ η : Fin d) (hne : η ≠ μ)
    (y u v : CTorus d L N₁ m₁ k) :
    q (((reflBase (L ^ j) μ (L ^ j : ZMod _) (u - y) + y) -
        (reflBase (L ^ j) μ (L ^ j : ZMod _) (v - y) + y)) μ) *
      q (((reflBase (L ^ j) μ (L ^ j : ZMod _) (u - y) + y) -
        (reflBase (L ^ j) μ (L ^ j : ZMod _) (v - y) + y)) η) =
      -(q ((u - v) μ) * q ((u - v) η)) := by
  rw [reflBase_sub_at_same, reflBase_sub_at_other μ η hne, hq]
  ring

omit [NeZero L] [NeZero N₁] in
/-- A coordinate exchange interchanges the two diagonal coordinate weights. -/
theorem pair_coord_weight_swap_at (q : ZMod (N₁ * L ^ m₁ * L ^ k) → ℂ)
    (μ η : Fin d) (y u v : CTorus d L N₁ m₁ k) :
    q (((swapJ μ η (u - y) + y) - (swapJ μ η (v - y) + y)) μ) ^ 2 =
      q ((u - v) η) ^ 2 := by
  rw [swapJ_sub_at_apply, Equiv.swap_apply_left]

open Classical in
/-- The full density Hessian pair sum at the origin is reindexed by exchange of coordinates.
The weight is arbitrary and remains visible on the transformed pair. -/
theorem LiftCtx.weightedHessian_swapJ (ctx : LiftCtx P β ν a Tm ρd Ek j ρ)
    (i₀ i₁ : Fin N) (μ η : Fin d)
    (w : CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → ℂ) :
    (∑ u ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
      ∑ v ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j 0 ψ
          (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
          (blockDir L j u i₁) (blockDir L j v i₁) * w u v) =
    ∑ u ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
      ∑ v ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j 0 ψ
          (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
          (blockDir L j u i₁) (blockDir L j v i₁) *
          w (swapJ μ η u) (swapJ μ η v) := by
  apply weighted_double_sum_invol _ (swapJ μ η) _ w
  · intro x
    change (swapJ μ η).symm ((swapJ μ η) x) = x
    exact Equiv.symm_apply_apply (swapJ μ η) x
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro ξ
    have := hx ((Equiv.swap μ η) ξ)
    change (x ((Equiv.swap μ η) ξ)).val % L ^ j = 0
    exact this
  · intro u hu v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact ctx.D2_Eloc_swapJ i₀ i₁ μ η u v |>.symm

open Classical in
/-- The same finite Hessian pair sum is reindexed by reflection of a coordinate about
the origin block. -/
theorem LiftCtx.weightedHessian_flipBy (ctx : LiftCtx P β ν a Tm ρd Ek j ρ)
    (i₀ i₁ : Fin N) (μ : Fin d)
    (w : CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → ℂ) :
    (∑ u ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
      ∑ v ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j 0 ψ
          (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
          (blockDir L j u i₁) (blockDir L j v i₁) * w u v) =
    ∑ u ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
      ∑ v ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j 0 ψ
          (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
          (blockDir L j u i₁) (blockDir L j v i₁) *
          w (reflBase (L ^ j) μ (L ^ j : ZMod _) u)
            (reflBase (L ^ j) μ (L ^ j : ZMod _) v) := by
  have hdvd : L ^ j ∣ (N₁ * L ^ m₁) * L ^ k :=
    (pow_dvd_pow L ctx.jk).trans (dvd_mul_left _ _)
  have hval : L ^ j ∣ ((L ^ j : ZMod (N₁ * L ^ m₁ * L ^ k))).val := by
    simpa only [Nat.cast_pow] using
      (dvd_val_natCast (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ctx.jk dvd_rfl)
  apply weighted_double_sum_invol _ (reflBase (L ^ j) μ (L ^ j : ZMod _)) _ w
  · intro x
    exact reflBase_reflBase _ _ _ _
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (aligned_reflBase_iff hdvd dvd_rfl μ (L ^ j : ZMod _)
      (by simpa only [Nat.cast_pow] using hval) x).2 hx
  · intro u hu v hv
    exact (ctx.D2_Eloc_flipBy i₀ i₁ μ u v).symm

open Classical in
/-- Coordinate exchange reindexes the full Hessian pair sum at every aligned centre. -/
theorem LiftCtx.weightedHessian_swapJ_at (ctx : LiftCtx P β ν a Tm ρd Ek j ρ)
    (i₀ i₁ : Fin N) {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (μ η : Fin d) (w : CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → ℂ) :
    (∑ u ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
      ∑ v ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ
          (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
          (blockDir L j u i₁) (blockDir L j v i₁) * w u v) =
    ∑ u ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
      ∑ v ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ
          (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
          (blockDir L j u i₁) (blockDir L j v i₁) *
          w (swapJ μ η (u - y) + y) (swapJ μ η (v - y) + y) := by
  have hdvd : L ^ j ∣ N₁ * L ^ m₁ * L ^ k := by
    exact (pow_dvd_pow L ctx.jk).trans (dvd_mul_left _ _)
  apply weighted_double_sum_invol _ (fun u => swapJ μ η (u - y) + y) _ w
  · intro x
    simp only [add_sub_cancel_right]
    have heq : swapJ μ η (swapJ μ η (x - y)) = x - y := by
      change (swapJ μ η).symm ((swapJ μ η) (x - y)) = x - y
      exact Equiv.symm_apply_apply (swapJ μ η) (x - y)
    rw [heq, sub_add_cancel]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have hsub : Aligned (L ^ j) (x - y) := by
      rw [sub_eq_add_neg]
      exact aligned_add hdvd hx (aligned_neg hdvd hy)
    exact aligned_add hdvd
      (aligned_swapJ μ η hsub) hy
  · intro u hu v hv
    exact (ctx.D2_Eloc_swapJ_at i₀ i₁ hy μ η u v).symm

open Classical in
/-- Coordinate reflection reindexes the full Hessian pair sum at every aligned centre. -/
theorem LiftCtx.weightedHessian_flipBy_at (ctx : LiftCtx P β ν a Tm ρd Ek j ρ)
    (i₀ i₁ : Fin N) {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (μ : Fin d) (w : CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → ℂ) :
    (∑ u ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
      ∑ v ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ
          (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
          (blockDir L j u i₁) (blockDir L j v i₁) * w u v) =
    ∑ u ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
      ∑ v ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ
          (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
          (blockDir L j u i₁) (blockDir L j v i₁) *
          w (reflBase (L ^ j) μ (L ^ j : ZMod _) (u - y) + y)
            (reflBase (L ^ j) μ (L ^ j : ZMod _) (v - y) + y) := by
  have hdvd : L ^ j ∣ N₁ * L ^ m₁ * L ^ k :=
    (pow_dvd_pow L ctx.jk).trans (dvd_mul_left _ _)
  have hval : L ^ j ∣ ((L ^ j : ZMod (N₁ * L ^ m₁ * L ^ k))).val := by
    simpa only [Nat.cast_pow] using
      (dvd_val_natCast (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ctx.jk dvd_rfl)
  apply weighted_double_sum_invol _
    (fun u => reflBase (L ^ j) μ (L ^ j : ZMod _) (u - y) + y) _ w
  · intro x
    simp only [add_sub_cancel_right, reflBase_reflBase, sub_add_cancel]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have hsub : Aligned (L ^ j) (x - y) := by
      rw [sub_eq_add_neg]
      exact aligned_add hdvd hx (aligned_neg hdvd hy)
    have hrefl : Aligned (L ^ j)
        (reflBase (L ^ j) μ (L ^ j : ZMod _) (x - y)) :=
      (aligned_reflBase_iff hdvd dvd_rfl μ (L ^ j : ZMod _)
        (by simpa only [Nat.cast_pow] using hval) (x - y)).2 hsub
    exact aligned_add hdvd hrefl hy
  · intro u hu v hv
    exact (ctx.D2_Eloc_flipBy_at i₀ i₁ hy μ u v).symm

open Classical in
/-- At every aligned centre, reflection cancels the raw Hessian pair sum with any odd
coordinate weight. The antipodal convention is encoded in the oddness hypothesis. -/
theorem LiftCtx.weightedHessian_pair_offdiag_zero_at
    (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ i₁ : Fin N)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (q : ZMod (N₁ * L ^ m₁ * L ^ k) → ℂ) (hq : ∀ x, q (-x) = -q x)
    (μ η : Fin d) (hne : η ≠ μ) :
    (∑ u ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
      ∑ v ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ
          (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
          (blockDir L j u i₁) (blockDir L j v i₁) *
          (q ((u - v) μ) * q ((u - v) η))) = 0 := by
  have h := ctx.weightedHessian_flipBy_at i₀ i₁ hy μ
    (fun u v => q ((u - v) μ) * q ((u - v) η))
  have hneg :
      (∑ u ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        ∑ v ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
          D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ
            (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
            (blockDir L j u i₁) (blockDir L j v i₁) *
            (q ((u - v) μ) * q ((u - v) η))) =
      -(∑ u ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        ∑ v ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
          D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ
            (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
            (blockDir L j u i₁) (blockDir L j v i₁) *
            (q ((u - v) μ) * q ((u - v) η))) := by
    simpa only [pair_coord_weight_flip_at q hq μ η hne y, mul_neg,
      Finset.sum_neg_distrib] using h
  exact CharZero.eq_neg_self_iff.mp hneg

open Classical in
/-- At every aligned centre, coordinate exchange identifies the diagonal Hessian pair
sums for an arbitrary coordinate weight. -/
theorem LiftCtx.weightedHessian_pair_diag_eq_at
    (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ i₁ : Fin N)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (q : ZMod (N₁ * L ^ m₁ * L ^ k) → ℂ) (μ η : Fin d) :
    (∑ u ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
      ∑ v ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ
          (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
          (blockDir L j u i₁) (blockDir L j v i₁) * q ((u - v) μ) ^ 2) =
    (∑ u ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
      ∑ v ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ
          (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
          (blockDir L j u i₁) (blockDir L j v i₁) * q ((u - v) η) ^ 2) := by
  have h := ctx.weightedHessian_swapJ_at i₀ i₁ hy μ η
    (fun u v => q ((u - v) μ) ^ 2)
  simp_rw [pair_coord_weight_swap_at q μ η y] at h
  exact h

end Balaban.SmallField.Def6
