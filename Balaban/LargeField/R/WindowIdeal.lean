module

public import Balaban.LargeField.R.WindowChain
public import Balaban.Background.Composition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Volume fractions of the layers of a block tree and the ideal composed weight (Lemma III.1.6, ideal case)

* `BlockTree.nBlocks`, `BlockTree.nLeaves`: the numbers of non-leaf blocks / leaves of a scale; the
  children count `m · N_{s+1} = N_s + Lf_s` (`children_count`);
* `frac_level`: `N_s w_s = ∑_{x : n_x < s} w_x` (the non-leaf blocks of scale `s` have the same total
  volume fraction as the leaves of smaller scale);
* `sum_scale`: `∑_y F(s_y) w_y = ∑_x w_x ∑_{s = n_x + 1}^k F(s)`;
* `composedWeight_ideal`: with `z ≡ 1` and the ideal coefficients `c_j = β_j a L^{d-2}`,
  `β_j = β_k L^{-(k-j)(d-2)}`, the composed weight `a^♮_z` is the weight `a_z` of P2 (4.7) = BG (6.5),
  `1/a_z = ∑_x w_x u_{k-n_x}`, `u_r = 1/compWeight L a r`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban.Background

namespace BlockTree

variable {m k1 k : ℕ} (B : BlockTree m k1 k)

/-- The number of non-leaf blocks of scale `s`. -/
def nBlocks (s : ℕ) : ℕ := ((Finset.range (B.n + 1)).filter fun i => B.scale i = s).card

/-- The number of leaves of scale `s`. -/
def nLeaves (s : ℕ) : ℕ := (Finset.univ.filter fun x : Fin B.nLeaf => B.leafScale x = s).card

theorem leafScale_ge (x : Fin B.nLeaf) : k1 ≤ B.leafScale x := by
  have := B.scale_ge (B.leafPar x) (B.leafPar_le x)
  unfold leafScale; omega

theorem leafScale_lt (x : Fin B.nLeaf) : B.leafScale x < k := by
  have := B.scale_ge (B.leafPar x) (B.leafPar_le x)
  have := B.scale_le (B.leafPar x) (B.leafPar_le x)
  unfold leafScale; omega

theorem scale_ne_zero_of_lt {i s : ℕ} (hs : s < k) (hi : B.scale i = s) : i ≠ 0 := by
  rintro rfl; rw [B.root_scale] at hi; omega

/-- Each non-leaf block of scale `s + 1` has `m` children: the non-leaf blocks and the leaves of scale `s`. -/
theorem children_count {s : ℕ} (hs : s < k) :
    m * B.nBlocks (s + 1) = B.nBlocks s + B.nLeaves s := by
  set T := (Finset.range (B.n + 1)).filter fun i => B.scale i = s + 1 with hT
  have h1 : m * B.nBlocks (s + 1) = ∑ i ∈ T, m := by
    simp [nBlocks, hT, mul_comm]
  have h2 : ∑ i ∈ T, m = ∑ i ∈ T, (((Finset.range (B.n + 1)).filter (fun c => c ≠ 0 ∧ B.par c = i)).card +
      (Finset.univ.filter (fun x : Fin B.nLeaf => B.leafPar x = i)).card) :=
    Finset.sum_congr rfl fun i hi => (B.full i (by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega)).symm
  rw [h1, h2, Finset.sum_add_distrib]
  congr 1
  · -- internal children
    have hS : (Finset.range (B.n + 1)).filter (fun i => B.scale i = s) =
        (Finset.range (B.n + 1)).filter (fun c => c ≠ 0 ∧ B.scale (B.par c) = s + 1) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hc, hcs⟩
        have h0 := B.scale_ne_zero_of_lt hs hcs
        exact ⟨hc, h0, by rw [B.scale_par c (by omega) h0, hcs]⟩
      · rintro ⟨hc, h0, hcs⟩
        exact ⟨hc, by have := B.scale_par c (by omega) h0; omega⟩
    unfold nBlocks
    rw [hS, Finset.card_eq_sum_card_fiberwise (f := B.par) (t := T) ?_]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : B.scale i = s + 1 := (Finset.mem_filter.mp hi).2
      congr 1
      ext c
      simp only [Finset.mem_filter, Finset.mem_range]
      have key : (c < B.n + 1 ∧ c ≠ 0 ∧ B.par c = i) ↔
          ((c < B.n + 1 ∧ c ≠ 0 ∧ B.scale (B.par c) = s + 1) ∧ B.par c = i) := by
        constructor
        · rintro ⟨hc, h0, hp⟩; exact ⟨⟨hc, h0, by rw [hp]; exact hi'⟩, hp⟩
        · rintro ⟨⟨hc, h0, _⟩, hp⟩; exact ⟨hc, h0, hp⟩
      exact key
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_coe, hT] at hc ⊢
      have := B.par_lt c (by omega) hc.2.1
      exact ⟨by omega, hc.2.2⟩
  · -- leaf children
    have hS : (Finset.univ.filter fun x : Fin B.nLeaf => B.leafScale x = s) =
        Finset.univ.filter fun x : Fin B.nLeaf => B.scale (B.leafPar x) = s + 1 := by
      ext x
      have := B.scale_ge (B.leafPar x) (B.leafPar_le x)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold leafScale
      constructor <;> intro h <;> omega
    unfold nLeaves
    rw [hS, Finset.card_eq_sum_card_fiberwise (f := B.leafPar) (t := T) ?_]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : B.scale i = s + 1 := (Finset.mem_filter.mp hi).2
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have key : B.leafPar x = i ↔ (B.scale (B.leafPar x) = s + 1 ∧ B.leafPar x = i) := by
        constructor
        · intro hp; exact ⟨by rw [hp]; exact hi', hp⟩
        · rintro ⟨_, hp⟩; exact hp
      exact key
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe, hT, Finset.mem_range] at hx ⊢
      exact ⟨by have := B.leafPar_le x; omega, hx⟩

theorem blockFrac_mul {s : ℕ} (hm : 0 < m) (hs : s < k) :
    blockFrac m k (s + 1) = m * blockFrac m k s := by
  rw [← blockFrac_succ hm hs]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

theorem nBlocks_zero_of_le {s : ℕ} (hs : s ≤ k1) : B.nBlocks s = 0 := by
  unfold nBlocks
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  have := B.scale_ge i (by have := Finset.mem_range.mp hi; omega)
  omega

/-- The non-leaf blocks of scale `s` have the same total volume fraction as the leaves of smaller scale. -/
theorem frac_level (hm : 0 < m) : ∀ s, s ≤ k →
    (B.nBlocks s : ℝ) * blockFrac m k s =
      ∑ x ∈ Finset.univ.filter (fun x : Fin B.nLeaf => B.leafScale x < s),
        blockFrac m k (B.leafScale x) := by
  intro s
  induction s with
  | zero =>
    intro _
    have : B.nBlocks 0 = 0 := B.nBlocks_zero_of_le (Nat.zero_le _)
    simp [this]
  | succ s ih =>
    intro hs
    have hsk : s < k := hs
    have h1 := B.children_count hsk
    have h2 : (m : ℝ) * (B.nBlocks (s + 1) : ℝ) = (B.nBlocks s : ℝ) + (B.nLeaves s : ℝ) := by
      exact_mod_cast h1
    rw [blockFrac_mul hm hsk]
    have hsplit : (Finset.univ.filter (fun x : Fin B.nLeaf => B.leafScale x < s + 1)) =
        (Finset.univ.filter (fun x : Fin B.nLeaf => B.leafScale x < s)) ∪
          (Finset.univ.filter (fun x : Fin B.nLeaf => B.leafScale x = s)) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]; omega
    rw [hsplit, Finset.sum_union (by
      rw [Finset.disjoint_left]; intro x hx hx'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'; omega), ← ih hsk.le]
    have h3 : ∑ x ∈ Finset.univ.filter (fun x : Fin B.nLeaf => B.leafScale x = s),
        blockFrac m k (B.leafScale x) = (B.nLeaves s : ℝ) * blockFrac m k s := by
      rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2])]
      simp [nLeaves]
    rw [h3]
    calc (B.nBlocks (s + 1) : ℝ) * (m * blockFrac m k s)
        = ((m : ℝ) * (B.nBlocks (s + 1) : ℝ)) * blockFrac m k s := by ring
      _ = _ := by rw [h2]; ring

/-- `∑_y F(s_y) w_y = ∑_x w_x ∑_{s = n_x + 1}^{k} F(s)`. -/
theorem sum_scale (hm : 0 < m) (F : ℕ → ℝ) :
    ∑ i ∈ Finset.range (B.n + 1), F (B.scale i) * blockFrac m k (B.scale i) =
      ∑ x : Fin B.nLeaf, blockFrac m k (B.leafScale x) *
        ∑ s ∈ Finset.Ioc (B.leafScale x) k, F s := by
  have h1 : ∑ i ∈ Finset.range (B.n + 1), F (B.scale i) * blockFrac m k (B.scale i) =
      ∑ s ∈ Finset.Ioc k1 k, ∑ i ∈ (Finset.range (B.n + 1)).filter (fun i => B.scale i = s),
        F (B.scale i) * blockFrac m k (B.scale i) :=
    (Finset.sum_fiberwise_of_maps_to (g := B.scale) (s := Finset.range (B.n + 1))
      (t := Finset.Ioc k1 k) (f := fun i => F (B.scale i) * blockFrac m k (B.scale i))
      (fun i hi => Finset.mem_Ioc.mpr ⟨by have := B.scale_ge i (by have := Finset.mem_range.mp hi; omega); omega,
        B.scale_le i (by have := Finset.mem_range.mp hi; omega)⟩)).symm
  rw [h1]
  have h2 : ∀ s ∈ Finset.Ioc k1 k, ∑ i ∈ (Finset.range (B.n + 1)).filter (fun i => B.scale i = s),
      F (B.scale i) * blockFrac m k (B.scale i) =
      ∑ x : Fin B.nLeaf, if B.leafScale x < s then F s * blockFrac m k (B.leafScale x) else 0 := by
    intro s hs
    have hsk := (Finset.mem_Ioc.mp hs).2
    rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [show (((Finset.range (B.n + 1)).filter (fun i => B.scale i = s)).card : ℝ) = B.nBlocks s from rfl]
    have hfl := B.frac_level hm s hsk
    rw [← Finset.sum_filter, ← Finset.mul_sum, ← hfl]
    ring
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, Finset.mul_sum]
  have hset : (Finset.Ioc k1 k).filter (fun s => B.leafScale x < s) = Finset.Ioc (B.leafScale x) k := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    have := B.leafScale_ge x
    omega
  rw [hset]
  exact Finset.sum_congr rfl fun s _ => by ring

end BlockTree

theorem sum_Ioc_reflect (G : ℕ → ℝ) {a k : ℕ} (h : a ≤ k) :
    ∑ s ∈ Finset.Ioc a k, G (k - s) = ∑ t ∈ Finset.range (k - a), G t := by
  refine Finset.sum_nbij' (fun s => k - s) (fun t => k - t) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp only [Finset.mem_Ioc, Finset.mem_range] at hs ⊢; omega
  · intro t ht; simp only [Finset.mem_Ioc, Finset.mem_range] at ht ⊢; omega
  · intro s hs; simp only [Finset.mem_Ioc] at hs; omega
  · intro t ht; simp only [Finset.mem_range] at ht; omega
  · intro s _; rfl

/-- `a · u_r = ∑_{t < r} L^{-2t}` for `u_r = 1/compWeight L a r`. -/
theorem geom_compWeight {L : ℕ} (hL : 2 ≤ L) {a : ℝ} (ha : 0 < a) (r : ℕ) :
    ∑ t ∈ Finset.range r, (((L : ℝ) ^ 2) ^ t)⁻¹ = a * (compWeight L a r)⁻¹ := by
  rw [compWeight_inv]
  have hL2 : (1 : ℝ) < (L : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
  set x : ℝ := (((L : ℝ) ^ 2))⁻¹ with hx
  have hx1 : x ≠ 1 := by
    rw [hx]; intro h; have := inv_eq_one.mp h; linarith
  have hx0 : x < 1 := by rw [hx]; exact inv_lt_one_of_one_lt₀ hL2
  have e1 : ∀ t : ℕ, (((L : ℝ) ^ 2) ^ t)⁻¹ = x ^ t := fun t => by rw [hx, inv_pow]
  simp_rw [e1]
  rw [geom_sum_eq hx1]
  have e2 : (((L : ℝ) ^ r) ^ 2)⁻¹ = x ^ r := by
    rw [hx, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  rw [e2]
  have : (1 - x) ≠ 0 := by linarith
  field_simp
  ring

/-- The ideal coefficients `c_j = β_j a L^{d-2}`, `β_j = β_k L^{-(k-j)(d-2)}`. -/
noncomputable def idealCoeff (L d k : ℕ) (βk a : ℝ) (j : ℕ) : ℝ :=
  βk * a * (L : ℝ) ^ (d - 2) / ((L : ℝ) ^ (d - 2)) ^ (k - j)

namespace BlockTree

variable {m k1 k : ℕ} (B : BlockTree m k1 k)

/-- The weight `a_z` of P2 (4.7) = BG (6.5): `1/a_z = ∑_x w_x u_{k - n_x}`, `u_r = 1/compWeight L a r`. -/
noncomputable def blockWeight (L : ℕ) (a : ℝ) : ℝ :=
  (∑ x : Fin B.nLeaf, blockFrac m k (B.leafScale x) * (compWeight L a (k - B.leafScale x))⁻¹)⁻¹

/-- `β_k a_z`-normalized sum: `∑_y ϖ_j² w_y² / c_j`, the inverse of `composedPrecision`. -/
noncomputable def precSum (c z : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (B.n + 1),
    varpi k z (B.scale i - 1) ^ 2 * blockFrac m k (B.scale i) ^ 2 / c (B.scale i - 1)

theorem composedPrecision_eq (c z : ℕ → ℝ) : B.composedPrecision c z = (B.precSum c z)⁻¹ := rfl

theorem varpi_one (n : ℕ) : varpi k (fun _ => (1 : ℝ)) n = 1 := by simp [varpi]

/-- The term of the non-leaf block `i` for the ideal coefficients and `z ≡ 1`. -/
theorem ideal_term {L d : ℕ} (hmL : m = L ^ d) (hL : 2 ≤ L) (hd : 2 ≤ d) {a βk : ℝ} (ha : 0 < a)
    (hβ : 0 < βk) {i : ℕ} (hi : i ∈ Finset.range (B.n + 1)) :
    varpi k (fun _ => (1 : ℝ)) (B.scale i - 1) ^ 2 * blockFrac m k (B.scale i) ^ 2 /
        idealCoeff L d k βk a (B.scale i - 1) =
      (βk * a)⁻¹ * ((((L : ℝ) ^ 2) ^ (k - B.scale i))⁻¹ * blockFrac m k (B.scale i)) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hge := B.scale_ge i (by have := Finset.mem_range.mp hi; omega)
  have hle := B.scale_le i (by have := Finset.mem_range.mp hi; omega)
  rw [varpi_one]
  unfold idealCoeff blockFrac
  have hk : k - (B.scale i - 1) = (k - B.scale i) + 1 := by omega
  rw [hk, pow_succ ((L : ℝ) ^ (d - 2)) (k - B.scale i)]
  have hx : (0 : ℝ) < ((L : ℝ) ^ (d - 2)) ^ (k - B.scale i) := by positivity
  have hy : (0 : ℝ) < ((L : ℝ) ^ 2) ^ (k - B.scale i) := by positivity
  have hxy : ((m : ℝ)) ^ (k - B.scale i) = ((L : ℝ) ^ (d - 2)) ^ (k - B.scale i) *
      ((L : ℝ) ^ 2) ^ (k - B.scale i) := by
    have hmR : (m : ℝ) = (L : ℝ) ^ d := by exact_mod_cast hmL
    rw [← mul_pow, ← pow_add, show d - 2 + 2 = d by omega, hmR]
  rw [hxy]
  set x := ((L : ℝ) ^ (d - 2)) ^ (k - B.scale i)
  set y := ((L : ℝ) ^ 2) ^ (k - B.scale i)
  have hL' : (0 : ℝ) < (L : ℝ) ^ (d - 2) := by positivity
  field_simp

/-- The inverse composed precision for the ideal data: `βk⁻¹ ∑_x w_x u_{k - n_x}`. -/
theorem precSum_ideal {L d : ℕ} (hmL : m = L ^ d) (hL : 2 ≤ L) (hd : 2 ≤ d) {a βk : ℝ}
    (ha : 0 < a) (hβ : 0 < βk) :
    B.precSum (idealCoeff L d k βk a) (fun _ => 1) =
      βk⁻¹ * ∑ x : Fin B.nLeaf, blockFrac m k (B.leafScale x) * (compWeight L a (k - B.leafScale x))⁻¹ := by
  have hm : 0 < m := by rw [hmL]; positivity
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  unfold precSum
  rw [Finset.sum_congr rfl fun i hi => B.ideal_term hmL hL hd ha hβ hi, ← Finset.mul_sum]
  rw [B.sum_scale hm (fun s => (((L : ℝ) ^ 2) ^ (k - s))⁻¹)]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_Ioc_reflect (fun t => (((L : ℝ) ^ 2) ^ t)⁻¹) (B.leafScale_lt x).le,
    geom_compWeight hL ha]
  field_simp

/-- **The ideal case of Lemma III.1.6**: with `z_i ≡ 1` and the ideal coefficients the composed weight `a^♮_z`
is the weight `a_z` of P2 (4.7) = BG (6.5). -/
theorem composedWeight_ideal {L d : ℕ} (hmL : m = L ^ d) (hL : 2 ≤ L) (hd : 2 ≤ d) {a βk : ℝ}
    (ha : 0 < a) (hβ : 0 < βk) :
    B.composedWeight βk (idealCoeff L d k βk a) (fun _ => 1) = B.blockWeight L a := by
  unfold composedWeight blockWeight
  rw [composedPrecision_eq, precSum_ideal B hmL hL hd ha hβ, mul_inv_rev, inv_inv]
  have hne : (βk : ℝ) ≠ 0 := hβ.ne'
  field_simp

end BlockTree

end Balaban.LargeField
