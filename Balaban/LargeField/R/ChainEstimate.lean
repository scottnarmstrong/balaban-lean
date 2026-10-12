module

public import Balaban.LargeField.R.ChainBound
public import Balaban.LargeField.R.ChainSeq
public import Balaban.LargeField.R.HatW
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The estimate of Lemma CH (Part III, Lemma III.4.4, (2.26′))

`chain_lt_hatW`: a chain `x₀, …, x_p` as in `chain_dist_le`, starting in the layer `j`, with all
vertices but the last in the layers `i₀ ≤ i < k`, `i₀ = max {k₁, j - h_k + 2}`, and with at most
`ν_max(k) (L M crit_k)^d` vertices in each layer (Lemma III.1.2 (c)), changes a field by
`< Ŵ_k c̄ δ̄_j`, where `(δ̄_i)` satisfies the hypotheses of Lemma III.4.4 (`IsAdmDelta`).
-/

@[expose] public section

namespace Balaban.LargeField

open Finset

/-- The first layer `i₀ = max {k₁, j - h_k + 2}` of Lemma III.4.3. -/
noncomputable def Setting.chainFloor (S : Setting) (k1 k j : ℕ) : ℕ := max k1 (j + 2 - S.h k)

theorem Setting.chainFloor_le {S : Setting} {k1 k j : ℕ} (hk1 : k1 ≤ j) :
    S.chainFloor k1 k j ≤ j := by
  unfold Setting.chainFloor
  have : 2 ≤ S.h k := by unfold Setting.h; omega
  omega

theorem Setting.le_chainFloor {S : Setting} (k1 k j : ℕ) : k1 ≤ S.chainFloor k1 k j :=
  le_max_left _ _

theorem Setting.sub_chainFloor_le {S : Setting} {k1 k j : ℕ} :
    j - S.chainFloor k1 k j ≤ S.h k - 2 := by
  unfold Setting.chainFloor
  omega

/-- **Lemma III.4.4, the estimate.** -/
theorem Setting.Ok.chain_lt_hatW {S : Setting} (hS : S.Ok) {ε : ℝ} {k1 k j : ℕ} (hk1 : k1 ≤ j)
    (hjk : j < k) {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε k1 k δ) {c : ℝ} (hc : 0 < c)
    {V E : Type*} [PseudoMetricSpace E] (ψ : V → E) (lay : V → ℕ) (x : ℕ → V) (p : ℕ)
    (hlay : ∀ m < p, S.chainFloor k1 k j ≤ lay (x m) ∧ lay (x m) < k)
    (hend : k ≤ lay (x p))
    (hstep : ∀ m < p, lay (x (m + 1)) = lay (x m) ∨ lay (x (m + 1)) + 1 = lay (x m) ∨
      lay (x m) + 1 = lay (x (m + 1)))
    (hintra : ∀ m < p, lay (x (m + 1)) = lay (x m) →
      dist (ψ (x m)) (ψ (x (m + 1))) ≤ c * δ (lay (x m)))
    (hcross₁ : ∀ m < p, lay (x (m + 1)) + 1 = lay (x m) →
      dist (ψ (x m)) (ψ (x (m + 1))) ≤ S.d * S.L * c * δ (lay (x (m + 1))))
    (hcross₂ : ∀ m < p, lay (x m) + 1 = lay (x (m + 1)) →
      dist (ψ (x m)) (ψ (x (m + 1))) ≤ S.d * S.L * c * δ (lay (x m)))
    (hcount : ∀ i, (((range p).filter fun m => lay (x m) = i).card : ℝ) ≤
      S.numax k * ((S.L : ℝ) * S.M * S.crit k) ^ S.d) :
    dist (ψ (x 0)) (ψ (x p)) < S.hatW ε k * c * δ j := by
  set i0 := S.chainFloor k1 k j with hi0
  have hi0j : i0 ≤ j := Setting.chainFloor_le hk1
  have hk1i0 : k1 ≤ i0 := Setting.le_chainFloor k1 k j
  have hdL : 1 ≤ S.d * S.L := by
    have := hS.three_le_d; have := hS.two_le_L
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hdL' : (1 : ℝ) ≤ S.d * S.L := by exact_mod_cast hdL
  have hδpos : ∀ i, k1 ≤ i → i < k → 0 < δ i := fun i h1 h2 => hδ.pos i h1 h2.le
  have hδnn : ∀ i, i0 ≤ i → i < k → 0 ≤ δ i := fun i h1 h2 =>
    (hδ.pos i (hk1i0.trans h1) h2.le).le
  have h1 := chain_dist_le ψ lay x p hdL hc.le δ hδnn hlay hend hstep hintra hcross₁ hcross₂ hcount
  -- the tail sum
  have htail : ∑ i ∈ Ico i0 k, δ i ≤ 4 * δ i0 := by
    refine le_trans ?_ (hδ.tail i0 hk1i0 (by omega))
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro i hi; rw [Finset.mem_Ico] at hi; rw [Finset.mem_Icc]; omega
    · intro i hi _
      rw [Finset.mem_Icc] at hi
      exact (hδ.pos i (hk1i0.trans hi.1) hi.2).le
  -- δ i0 ≤ e^ε L^{(d-2)/2 (h-2)} δ j
  have hLge : (1 : ℝ) ≤ S.L := hS.hatW_one_le_L
  have hgrow := hδ.growth i0 j hk1i0 hi0j hjk.le
  have hexp : (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2 * ((j : ℝ) - i0)) ≤
      (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2 * ((S.h k : ℝ) - 2)) := by
    apply Real.rpow_le_rpow_of_exponent_le hLge
    have hd3 : (3 : ℝ) ≤ S.d := by exact_mod_cast hS.three_le_d
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have := Setting.sub_chainFloor_le (S := S) (k1 := k1) (k := k) (j := j)
    have h2 : 2 ≤ S.h k := by unfold Setting.h; omega
    have : ((j - i0 : ℕ) : ℝ) ≤ ((S.h k - 2 : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sub hi0j, Nat.cast_sub h2] at this
    push_cast at this
    linarith
  have hδj := hδpos j (hk1.trans le_rfl) hjk
  have hLpos : (0 : ℝ) < S.L := hS.hatW_pos_L
  have hE : 0 < Real.exp ε := Real.exp_pos ε
  have hδ0 : δ i0 ≤ Real.exp ε * (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2 * ((S.h k : ℝ) - 2)) * δ j :=
    hgrow.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp hE.le) hδj.le)
  -- assemble
  have hν : (1 : ℝ) ≤ S.numax k := by exact_mod_cast hS.hatW_numax_ge_one k
  have hM : (1 : ℝ) ≤ S.M := by exact_mod_cast hS.one_le_M
  have hcrit : (0 : ℝ) < S.crit k := by
    have : 0 < S.crit k := by unfold Setting.crit; omega
    exact_mod_cast this
  set B : ℝ := S.numax k * ((S.L : ℝ) * S.M * S.crit k) ^ S.d with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  set X : ℝ := Real.exp ε * (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2 * ((S.h k : ℝ) - 2)) * δ j with hX
  have hXpos : 0 < X := by rw [hX]; positivity
  have hP : 0 < 2 * (S.d : ℝ) * S.L * c * B := by
    have : (0 : ℝ) < S.d := by have := hS.three_le_d; exact_mod_cast (by omega : 0 < S.d)
    positivity
  have h2 : 2 * (S.d : ℝ) * S.L * c * B * ∑ i ∈ Ico i0 k, δ i ≤
      2 * (S.d : ℝ) * S.L * c * B * (4 * X) :=
    mul_le_mul_of_nonneg_left (htail.trans (by linarith)) hP.le
  have h3 : 2 * (S.d : ℝ) * S.L * c * B * (4 * X) < S.hatW ε k * c * δ j := by
    have hW : S.hatW ε k = 4 * (1 + 2 * S.d * S.L) * B *
        (Real.exp ε * (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2 * ((S.h k : ℝ) - 2))) := by
      unfold Setting.hatW; rw [hB]; ring
    rw [hW, hX]
    have hq : 0 < c * B * (Real.exp ε * (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2 * ((S.h k : ℝ) - 2))) *
        δ j := by positivity
    nlinarith
  exact lt_of_le_of_lt (h1.trans h2) h3

end Balaban.LargeField
