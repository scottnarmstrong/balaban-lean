/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.LF1.BlockArith
public import Balaban.Green.BlockPoincareSharp
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Block averages of vector fields, bond energies, and Lemmas II.4.2–II.4.3

For a field `φ : Torus d ℓ → E` with values in an inner product space `E` (for the hard-spin
lemma, `E = ℝ^N`), the block average `bavg N m φ : Torus d m → E`, the directional bond energy
`bondEdir μ S φ = ∑_{x, x+e_μ ∈ S} ‖φ(x+e_μ) - φ(x)‖²` and `bondE S φ = ∑_μ bondEdir μ S φ`.

* `adjacent_blockAvg_sq_le` (Lemma II.4.2): for the adjacent blocks `y`, `y + e_μ` of side `N`,
  `‖Qφ(y) - Qφ(y + e_μ)‖² ≤ N^{2-d} · bondEdir μ (B_y ∪ B_{y+e_μ}) φ`.
* `hardSpin_one_sub_sq_le` (Lemma II.4.3): if `‖φ‖ = 1` on the block `B`,
  `1 - ‖Qφ(y)‖² ≤ ½ N^{2-d} bondE B φ`, using the landed `Balaban.blockPoincare_sharp`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Finset

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem sq_norm_sum_le {ι : Type*} (s : Finset ι) (v : ι → E) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ s.card * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  calc ‖∑ i ∈ s, v i‖ ^ 2 ≤ (∑ i ∈ s, ‖v i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := sq_sum_le_card_mul_sum_sq

/-- Jensen: `‖K⁻¹ ∑_{i∈s} v i‖² ≤ K⁻¹ ∑ ‖v i‖²` when `|s| = K`. -/
theorem sq_norm_avg_le {ι : Type*} (s : Finset ι) (v : ι → E) {K : ℝ} (hK : (s.card : ℝ) = K)
    (hK0 : 0 < K) : ‖K⁻¹ • ∑ i ∈ s, v i‖ ^ 2 ≤ K⁻¹ * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  rw [norm_smul, mul_pow, norm_inv, Real.norm_of_nonneg hK0.le, inv_pow]
  have := sq_norm_sum_le s v
  rw [hK] at this
  have hK2 : 0 < K ^ 2 := by positivity
  rw [inv_mul_le_iff₀ hK2]
  calc ‖∑ i ∈ s, v i‖ ^ 2 ≤ K * ∑ i ∈ s, ‖v i‖ ^ 2 := this
    _ = K ^ 2 * (K⁻¹ * ∑ i ∈ s, ‖v i‖ ^ 2) := by field_simp

end Basic

section Bonds

variable {E : Type*} [NormedAddCommGroup E] {d ℓ : ℕ}

/-- The square of the bond difference `‖φ(x + e_μ) - φ(x)‖²`. -/
noncomputable def bondTerm [NeZero ℓ] (φ : Torus d ℓ → E) (μ : Fin d) (x : Torus d ℓ) : ℝ :=
  ‖φ (x + Pi.single μ 1) - φ x‖ ^ 2

/-- The energy of the bonds `{x, x + e_μ}` with both end points in `S`. -/
noncomputable def bondEdir [NeZero ℓ] (μ : Fin d) (S : Finset (Torus d ℓ)) (φ : Torus d ℓ → E) :
    ℝ :=
  ∑ x, if x ∈ S ∧ x + Pi.single μ 1 ∈ S then bondTerm φ μ x else 0

/-- The energy of all bonds with both end points in `S`. -/
noncomputable def bondE [NeZero ℓ] (S : Finset (Torus d ℓ)) (φ : Torus d ℓ → E) : ℝ :=
  ∑ μ : Fin d, bondEdir μ S φ

variable [NeZero ℓ]

theorem bondTerm_nonneg (φ : Torus d ℓ → E) (μ : Fin d) (x : Torus d ℓ) : 0 ≤ bondTerm φ μ x :=
  by unfold bondTerm; positivity

theorem bondEdir_nonneg (μ : Fin d) (S : Finset (Torus d ℓ)) (φ : Torus d ℓ → E) :
    0 ≤ bondEdir μ S φ :=
  Finset.sum_nonneg fun x _ => by split_ifs; exacts [bondTerm_nonneg φ μ x, le_rfl]

theorem bondE_nonneg (S : Finset (Torus d ℓ)) (φ : Torus d ℓ → E) : 0 ≤ bondE S φ :=
  Finset.sum_nonneg fun μ _ => bondEdir_nonneg μ S φ

theorem bondEdir_mono {μ : Fin d} {S S' : Finset (Torus d ℓ)} (h : S ⊆ S') (φ : Torus d ℓ → E) :
    bondEdir μ S φ ≤ bondEdir μ S' φ :=
  Finset.sum_le_sum fun x _ => by
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨h h1.1, h h1.2⟩ h2
    · exact bondTerm_nonneg φ μ x
    · exact le_rfl

theorem bondE_mono {S S' : Finset (Torus d ℓ)} (h : S ⊆ S') (φ : Torus d ℓ → E) :
    bondE S φ ≤ bondE S' φ :=
  Finset.sum_le_sum fun _ _ => bondEdir_mono h φ

end Bonds

section Avg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d ℓ N m : ℕ}

/-- The block average `Qφ(y) = (N^d)⁻¹ ∑_{x ∈ B_y} φ(x)` of a vector-valued field. -/
noncomputable def bavg [NeZero ℓ] (N m : ℕ) (φ : Torus d ℓ → E) (y : Torus d m) : E :=
  ((N : ℝ) ^ d)⁻¹ • ∑ x ∈ blockFibre N m y, φ x

end Avg

section Lemma242

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d ℓ N m : ℕ} [NeZero ℓ]

omit [NeZero ℓ] in
theorem single_natCast_succ (μ : Fin d) (t : ℕ) :
    (Pi.single μ ((t + 1 : ℕ) : ZMod ℓ) : Torus d ℓ) =
      Pi.single μ (t : ZMod ℓ) + Pi.single μ 1 := by
  rw [Nat.cast_succ, Pi.single_add]

/-- **Lemma II.4.2** (adjacent block averages). -/
theorem adjacent_blockAvg_sq_le (hℓ : ℓ = N * m) (φ : Torus d ℓ → E) (y : Torus d m) (μ : Fin d) :
    ‖bavg N m φ y - bavg N m φ (y + Pi.single μ 1)‖ ^ 2 ≤
      (N : ℝ) ^ 2 * ((N : ℝ) ^ d)⁻¹ *
        bondEdir μ (blockFibre N m y ∪ blockFibre N m (y + Pi.single μ 1)) φ := by
  have hN := pos_left_of_eq hℓ
  have hm := pos_right_of_eq hℓ
  have : NeZero m := ⟨hm.ne'⟩
  set B := (blockFibre N m y : Finset (Torus d ℓ)) with hB
  set B' := (blockFibre N m (y + Pi.single μ 1) : Finset (Torus d ℓ)) with hB'
  set s : Torus d ℓ := Pi.single μ (N : ZMod ℓ) with hs
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  -- (i) translation by one block side
  have hbij : ∑ x' ∈ B', φ x' = ∑ x ∈ B, φ (x + s) := by
    refine (Finset.sum_nbij' (fun x => x + s) (fun x' => x' - s) ?_ ?_ ?_ ?_ ?_).symm
    · intro x hx
      rw [hB, mem_blockFibre] at hx
      rw [hB', mem_blockFibre, hs, blockMap_add_single_side hℓ, hx]
    · intro x' hx'
      rw [hB', mem_blockFibre] at hx'
      rw [hB, mem_blockFibre, hs, blockMap_sub_single_side hℓ, hx']; simp
    · intro x _; simp
    · intro x' _; simp
    · intro x _; rfl
  -- (ii) the difference as a sum of increments
  have hdiff : bavg N m φ y - bavg N m φ (y + Pi.single μ 1) =
      -(((N : ℝ) ^ d)⁻¹ • ∑ x ∈ B, ∑ t ∈ range N,
        (φ (x + Pi.single μ (((t + 1 : ℕ)) : ZMod ℓ)) - φ (x + Pi.single μ (t : ZMod ℓ)))) := by
    have htel : ∀ x : Torus d ℓ, ∑ t ∈ range N,
        (φ (x + Pi.single μ (((t + 1 : ℕ)) : ZMod ℓ)) - φ (x + Pi.single μ (t : ZMod ℓ))) =
        φ (x + s) - φ x := by
      intro x
      have := Finset.sum_range_sub (fun t : ℕ => φ (x + Pi.single μ (t : ZMod ℓ))) N
      simpa [hs] using this
    simp only [htel, Finset.sum_sub_distrib]
    unfold bavg
    rw [← hB, ← hB', hbij, ← smul_sub, ← smul_neg, neg_sub]
  -- (iii) Cauchy-Schwarz
  set v : Torus d ℓ → ℕ → E := fun x t =>
    φ (x + Pi.single μ (((t + 1 : ℕ)) : ZMod ℓ)) - φ (x + Pi.single μ (t : ZMod ℓ)) with hv
  have hcard : ((B ×ˢ range N).card : ℝ) = (N : ℝ) ^ d * N := by
    rw [Finset.card_product, Finset.card_range, hB, card_blockFibre hℓ]; push_cast; ring
  have hCS : ‖∑ x ∈ B, ∑ t ∈ range N, v x t‖ ^ 2 ≤ (N : ℝ) ^ d * N * ∑ x ∈ B, ∑ t ∈ range N, ‖v x t‖ ^ 2 := by
    have := sq_norm_sum_le (B ×ˢ range N) (fun p => v p.1 p.2)
    rw [Finset.sum_product, Finset.sum_product, hcard] at this
    exact this
  -- (iv) each increment is a bond with both end points in `B ∪ B'`
  have hbond : ∀ t ∈ range N, ∑ x ∈ B, ‖v x t‖ ^ 2 ≤ bondEdir μ (B ∪ B') φ := by
    intro t ht
    have htN : t < N := Finset.mem_range.1 ht
    set g : Torus d ℓ → ℝ := fun z => if z ∈ B ∪ B' ∧ z + Pi.single μ 1 ∈ B ∪ B' then bondTerm φ μ z else 0
      with hg
    have hmemB : ∀ x ∈ B, ∀ t' : ℕ, t' ≤ N → x + Pi.single μ (t' : ZMod ℓ) ∈ B ∪ B' := by
      intro x hx t' ht'
      rw [hB, mem_blockFibre] at hx
      rcases blockMap_add_single_cases hℓ x μ ht' with h | h
      · exact Finset.mem_union_left _ (by rw [hB, mem_blockFibre, h, hx])
      · exact Finset.mem_union_right _ (by rw [hB', mem_blockFibre, h, hx])
    have e1 : ∀ x ∈ B, ‖v x t‖ ^ 2 = g (x + Pi.single μ (t : ZMod ℓ)) := by
      intro x hx
      have h1 := hmemB x hx t htN.le
      have h2 := hmemB x hx (t + 1) htN
      have e : x + Pi.single μ (t : ZMod ℓ) + Pi.single μ 1 =
          x + Pi.single μ (((t + 1 : ℕ)) : ZMod ℓ) := by rw [single_natCast_succ, add_assoc]
      have hc : x + Pi.single μ (t : ZMod ℓ) ∈ B ∪ B' ∧
          x + Pi.single μ (t : ZMod ℓ) + Pi.single μ 1 ∈ B ∪ B' := ⟨h1, by rw [e]; exact h2⟩
      have : g (x + Pi.single μ (t : ZMod ℓ)) = bondTerm φ μ (x + Pi.single μ (t : ZMod ℓ)) := by
        rw [hg]; simp only [hc, and_self, ite_true]
      rw [this]
      unfold bondTerm
      rw [e, hv]
    rw [Finset.sum_congr rfl e1]
    have hinj : Function.Injective (fun x : Torus d ℓ => x + Pi.single μ (t : ZMod ℓ)) :=
      fun a b h => add_right_cancel h
    calc ∑ x ∈ B, g (x + Pi.single μ (t : ZMod ℓ))
        = ∑ z ∈ B.image (fun x => x + Pi.single μ (t : ZMod ℓ)), g z :=
          (Finset.sum_image (fun a _ b _ h => hinj h)).symm
      _ ≤ ∑ z, g z := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _ => by
          rw [hg]; simp only; split_ifs; exacts [bondTerm_nonneg φ μ z, le_rfl])
      _ = bondEdir μ (B ∪ B') φ := rfl
  have hsum : ∑ x ∈ B, ∑ t ∈ range N, ‖v x t‖ ^ 2 ≤ N * bondEdir μ (B ∪ B') φ := by
    rw [Finset.sum_comm]
    calc ∑ t ∈ range N, ∑ x ∈ B, ‖v x t‖ ^ 2 ≤ ∑ _t ∈ range N, bondEdir μ (B ∪ B') φ :=
          Finset.sum_le_sum hbond
      _ = _ := by simp
  rw [hdiff, norm_neg, norm_smul, mul_pow, norm_inv, norm_pow, Real.norm_natCast, inv_pow]
  have h0 : 0 ≤ bondEdir μ (B ∪ B') φ := bondEdir_nonneg _ _ _
  have hfin : ‖∑ x ∈ B, ∑ t ∈ range N, v x t‖ ^ 2 ≤
      (N : ℝ) ^ d * N * (N * bondEdir μ (B ∪ B') φ) :=
    hCS.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have : (((N : ℝ) ^ d) ^ 2)⁻¹ * ‖∑ x ∈ B, ∑ t ∈ range N, v x t‖ ^ 2 ≤
      (((N : ℝ) ^ d) ^ 2)⁻¹ * ((N : ℝ) ^ d * N * (N * bondEdir μ (B ∪ B') φ)) :=
    mul_le_mul_of_nonneg_left hfin (by positivity)
  refine this.trans (le_of_eq ?_)
  field_simp

end Lemma242

section HardSpin

variable {Nspin d ℓ N m : ℕ} [NeZero ℓ]

theorem sum_blockFibre_eq_smul_bavg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hℓ : ℓ = N * m) (φ : Torus d ℓ → E) (y : Torus d m) :
    ∑ x ∈ blockFibre N m y, φ x = ((N : ℝ) ^ d) • bavg N m φ y := by
  have hN := pos_left_of_eq hℓ
  have hNd : ((N : ℝ) ^ d) ≠ 0 := by positivity
  unfold bavg
  rw [smul_smul, mul_inv_cancel₀ hNd, one_smul]

/-- For unit vectors `φ` on the block, `N^d (1 - ‖Qφ‖²) = ∑_B ‖φ - Qφ‖²`. -/
theorem blockVariance_eq (hℓ : ℓ = N * m) (φ : Torus d ℓ → EuclideanSpace ℝ (Fin Nspin))
    (y : Torus d m) (h1 : ∀ x ∈ blockFibre N m y, ‖φ x‖ = 1) :
    ((N : ℝ) ^ d) * (1 - ‖bavg N m φ y‖ ^ 2) =
      ∑ x ∈ blockFibre N m y, ‖φ x - bavg N m φ y‖ ^ 2 := by
  have : NeZero m := ⟨(pos_right_of_eq hℓ).ne'⟩
  set q := bavg N m φ y with hq
  have hcard : ((blockFibre N m y : Finset (Torus d ℓ)).card : ℝ) = (N : ℝ) ^ d := by
    rw [card_blockFibre hℓ]; push_cast; ring
  have e1 : ∀ x ∈ (blockFibre N m y : Finset (Torus d ℓ)),
      ‖φ x - q‖ ^ 2 = 1 - 2 * inner ℝ (φ x) q + ‖q‖ ^ 2 := by
    intro x hx
    rw [norm_sub_sq_real, h1 x hx]; ring
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← sum_inner, sum_blockFibre_eq_smul_bavg hℓ φ y, ← hq, inner_smul_left]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard, mul_one, conj_trivial, real_inner_self_eq_norm_sq]
  ring

/-- **Lemma II.4.3** (hard-spin block bound). -/
theorem hardSpin_one_sub_sq_le (hℓ : ℓ = N * m) (φ : Torus d ℓ → EuclideanSpace ℝ (Fin Nspin))
    (y : Torus d m) (h1 : ∀ x ∈ blockFibre N m y, ‖φ x‖ = 1) :
    1 - ‖bavg N m φ y‖ ^ 2 ≤
      (1 / 2) * (N : ℝ) ^ 2 * ((N : ℝ) ^ d)⁻¹ * bondE (blockFibre N m y) φ := by
  have hN := pos_left_of_eq hℓ
  have hm := pos_right_of_eq hℓ
  have : NeZero m := ⟨hm.ne'⟩
  set B := (blockFibre N m y : Finset (Torus d ℓ)) with hB
  set q := bavg N m φ y with hq
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  -- the scalar fields `f_c = 1_B φ_c`
  set f : Fin Nspin → Torus d ℓ → ℝ := fun c x => if x ∈ B then φ x c else 0 with hf
  have hP : ∀ c x, blockProjection N m (f c) x = if x ∈ B then q c else 0 := by
    intro c x
    rw [blockProjection_apply, blockAverage_apply]
    by_cases hx : x ∈ B
    · have hbx : blockMap N m x = y := mem_blockFibre.1 hx
      have : ∑ x' ∈ blockFibre N m (blockMap N m x), f c x' = ∑ x' ∈ B, φ x' c := by
        rw [hbx]
        exact Finset.sum_congr rfl fun x' hx' => by rw [hf]; simp [hx']
      rw [this]; simp only [hx, ↓reduceIte]
      have h2 := congrArg (fun v => v c) (sum_blockFibre_eq_smul_bavg hℓ φ y)
      simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at h2
      rw [← hB] at h2
      rw [h2, ← mul_assoc, inv_mul_cancel₀ hNd.ne', one_mul]
    · simp only [hx, ↓reduceIte]
      have : ∑ x' ∈ blockFibre N m (blockMap N m x), f c x' = 0 := by
        refine Finset.sum_eq_zero fun x' hx' => ?_
        have hbx' : blockMap N m x' = blockMap N m x := mem_blockFibre.1 hx'
        have : x' ∉ B := by
          intro hxB
          exact hx (mem_blockFibre.2 (hbx'.symm.trans (mem_blockFibre.1 hxB)))
        rw [hf]; simp [this]
      rw [this]; simp
  -- variance
  have hvar : ∑ c, ∑ x, (f c x - blockProjection N m (f c) x) ^ 2 =
      ∑ x ∈ B, ‖φ x - q‖ ^ 2 := by
    rw [Finset.sum_comm]
    have : ∀ x : Torus d ℓ, ∑ c, (f c x - blockProjection N m (f c) x) ^ 2 =
        if x ∈ B then ‖φ x - q‖ ^ 2 else 0 := by
      intro x
      rw [EuclideanSpace.real_norm_sq_eq]
      have hfx : ∀ c, f c x = if x ∈ B then φ x c else 0 := fun _ => rfl
      by_cases hx : x ∈ B
      · simp only [hfx, hP, hx, ↓reduceIte]
        simp
      · simp only [hfx, hP, hx, ↓reduceIte]
        simp
    rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.sum_filter]
    congr 1
    ext x; simp [hB]
  -- inner energy
  have hinner : ∑ c, innerEnergy N (f c) ≤ bondE B φ := by
    have hfx : ∀ c x, f c x = if x ∈ B then φ x c else 0 := fun _ _ => rfl
    calc ∑ c, innerEnergy N (f c) = ∑ x : Torus d ℓ, ∑ μ : Fin d, ∑ c : Fin Nspin,
          (if (x μ).val % N + 1 < N then (f c (x + Pi.single μ 1) - f c x) ^ 2 else 0) := by
          unfold innerEnergy
          simp only [update_eq_add_single]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
      _ ≤ ∑ x : Torus d ℓ, ∑ μ : Fin d,
          (if x ∈ B ∧ x + Pi.single μ 1 ∈ B then bondTerm φ μ x else 0) := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun μ _ => ?_
          by_cases hc : (x μ).val % N + 1 < N
          · have hb := blockMap_add_single_one_of_mod hℓ x μ hc
            by_cases hx : x ∈ B
            · have hx' : x + Pi.single μ 1 ∈ B := by
                rw [hB, mem_blockFibre] at hx ⊢; rw [hb, hx]
              simp only [hc, hx, hx', and_self, ↓reduceIte, hfx]
              unfold bondTerm
              rw [EuclideanSpace.real_norm_sq_eq]
              simp
            · have hx' : x + Pi.single μ 1 ∉ B := by
                intro h'; apply hx
                rw [hB, mem_blockFibre] at h' ⊢; rw [← hb, h']
              simp only [hc, hx, hx', hfx, ↓reduceIte]
              simp
          · simp only [hc, ↓reduceIte]
            simp only [Finset.sum_const_zero]
            split_ifs
            · exact bondTerm_nonneg φ μ x
            · exact le_rfl
      _ = bondE B φ := by
          unfold bondE bondEdir
          rw [Finset.sum_comm]
  have hpoin : ∀ c, ∑ x, (f c x - blockProjection N m (f c) x) ^ 2 ≤
      (1 / 2) * (N : ℝ) ^ 2 * innerEnergy N (f c) := fun c => blockPoincare_sharp hℓ hN (f c)
  have h3 : ∑ x ∈ B, ‖φ x - q‖ ^ 2 ≤ (1 / 2) * (N : ℝ) ^ 2 * bondE B φ := by
    rw [← hvar]
    calc ∑ c, ∑ x, (f c x - blockProjection N m (f c) x) ^ 2
        ≤ ∑ c, (1 / 2) * (N : ℝ) ^ 2 * innerEnergy N (f c) := Finset.sum_le_sum fun c _ => hpoin c
      _ = (1 / 2) * (N : ℝ) ^ 2 * ∑ c, innerEnergy N (f c) := by rw [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hinner (by positivity)
  have h4 := blockVariance_eq hℓ φ y h1
  rw [← hq] at h4
  have h5 : 1 - ‖q‖ ^ 2 = ((N : ℝ) ^ d)⁻¹ * ∑ x ∈ B, ‖φ x - q‖ ^ 2 := by
    rw [← h4, ← mul_assoc, inv_mul_cancel₀ hNd.ne', one_mul]
  rw [h5]
  calc ((N : ℝ) ^ d)⁻¹ * ∑ x ∈ B, ‖φ x - q‖ ^ 2
      ≤ ((N : ℝ) ^ d)⁻¹ * ((1 / 2) * (N : ℝ) ^ 2 * bondE B φ) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

end HardSpin


end Balaban.LargeField
