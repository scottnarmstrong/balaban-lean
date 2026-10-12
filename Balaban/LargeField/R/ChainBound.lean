module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The counting part of Lemma CH (Part III, Lemma III.4.4, proof of the count)

A chain `x₀, …, x_p` in the graph `𝒢` of Definition III.4.1, seen only through the layer function
`lay`: consecutive vertices lie in the same layer (an intra edge) or in layers differing by one (a
cross edge); every vertex but the last lies in a layer `i₀ ≤ i < k`; `B` bounds the number of chain
vertices of each layer (the chain visits each vertex once, and a layer has at most `B` vertices).

`chain_dist_le`: if the field changes by at most `c̄ δ̄_i` along an intra edge of layer `i` and by at
most `d L c̄ δ̄_i` along a cross edge between layers `i + 1` and `i`, then
`dist (ψ x₀) (ψ x_p) ≤ 2 d L c̄ B ∑_{i=i₀}^{k-1} δ̄_i`.  (The source counts `B_i` intra and `2B_i` cross
edges per layer, i.e. the constant `1 + 2dL` in place of the `2dL` obtained here by charging every
edge to its lower end; the latter is smaller.)
-/

@[expose] public section

namespace Balaban.LargeField

open Finset

/-- **Charging argument.** See the module docstring. -/
theorem chain_dist_le {V E : Type*} [PseudoMetricSpace E] (ψ : V → E) (lay : V → ℕ) (x : ℕ → V)
    (p : ℕ) {d L : ℕ} (hdL : 1 ≤ d * L) {c : ℝ} (hc : 0 ≤ c) (δ : ℕ → ℝ) {i0 k : ℕ}
    (hδ : ∀ i, i0 ≤ i → i < k → 0 ≤ δ i)
    (hlay : ∀ m < p, i0 ≤ lay (x m) ∧ lay (x m) < k)
    (hend : k ≤ lay (x p))
    (hstep : ∀ m < p, lay (x (m + 1)) = lay (x m) ∨ lay (x (m + 1)) + 1 = lay (x m) ∨
      lay (x m) + 1 = lay (x (m + 1)))
    (hintra : ∀ m < p, lay (x (m + 1)) = lay (x m) →
      dist (ψ (x m)) (ψ (x (m + 1))) ≤ c * δ (lay (x m)))
    (hcross₁ : ∀ m < p, lay (x (m + 1)) + 1 = lay (x m) →
      dist (ψ (x m)) (ψ (x (m + 1))) ≤ d * L * c * δ (lay (x (m + 1))))
    (hcross₂ : ∀ m < p, lay (x m) + 1 = lay (x (m + 1)) →
      dist (ψ (x m)) (ψ (x (m + 1))) ≤ d * L * c * δ (lay (x m)))
    {B : ℝ} (hcount : ∀ i, (((range p).filter fun m => lay (x m) = i).card : ℝ) ≤ B) :
    dist (ψ (x 0)) (ψ (x p)) ≤ 2 * d * L * c * B * ∑ i ∈ Ico i0 k, δ i := by
  have hdL' : (1 : ℝ) ≤ d * L := by exact_mod_cast hdL
  set w : ℕ → ℝ := fun m => d * L * c * δ (lay (x m)) with hw
  have hw0 : ∀ m < p, 0 ≤ w m := fun m hm => by
    have := hδ _ (hlay m hm).1 (hlay m hm).2
    simp only [hw]; positivity
  -- each edge is bounded by w m or by w (m+1), the latter only when m + 1 < p
  have hedge : ∀ m < p, dist (ψ (x m)) (ψ (x (m + 1))) ≤
      w m + (if m + 1 < p then w (m + 1) else 0) := by
    intro m hm
    have hwm := hw0 m hm
    have hnext : 0 ≤ (if m + 1 < p then w (m + 1) else 0) := by
      split_ifs with h
      · exact hw0 _ h
      · exact le_rfl
    rcases hstep m hm with h | h | h
    · refine (hintra m hm h).trans ?_
      have := hδ _ (hlay m hm).1 (hlay m hm).2
      simp only [hw]
      nlinarith [mul_nonneg hc this]
    · -- x (m+1) is the lower end
      have hlt : m + 1 < p := by
        by_contra hge
        have : m + 1 = p := by omega
        have h1 := (hlay m hm).2
        rw [this] at h
        omega
      refine (hcross₁ m hm h).trans ?_
      simp only [hw, hlt, ite_true]
      linarith
    · refine (hcross₂ m hm h).trans ?_
      simp only [hw]
      linarith
  have hsum1 : dist (ψ (x 0)) (ψ (x p)) ≤
      ∑ m ∈ range p, (w m + (if m + 1 < p then w (m + 1) else 0)) := by
    refine (dist_le_range_sum_dist (fun m => ψ (x m)) p).trans ?_
    exact Finset.sum_le_sum fun m hm => hedge m (Finset.mem_range.1 hm)
  have hshift : ∑ m ∈ range p, (if m + 1 < p then w (m + 1) else 0) ≤ ∑ m ∈ range p, w m := by
    rcases Nat.eq_zero_or_pos p with h0 | hp
    · subst h0; simp
    · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      rw [Finset.sum_range_succ, Finset.sum_range_succ' w]
      have e : ∑ m ∈ range q, (if m + 1 < q + 1 then w (m + 1) else 0) = ∑ m ∈ range q, w (m + 1) :=
        Finset.sum_congr rfl fun m hm => by
          have : m + 1 < q + 1 := by have := Finset.mem_range.1 hm; omega
          simp [this]
      rw [e]
      simp only [show ¬ (q + 1 < q + 1) from lt_irrefl _, ite_false, add_zero]
      have : 0 ≤ w 0 := hw0 0 (by omega)
      linarith
  have hsum2 : dist (ψ (x 0)) (ψ (x p)) ≤ 2 * ∑ m ∈ range p, w m := by
    rw [Finset.sum_add_distrib] at hsum1
    linarith
  -- group by layers
  have hgroup : ∑ m ∈ range p, w m ≤ d * L * c * B * ∑ i ∈ Ico i0 k, δ i := by
    have hmaps : ∀ m ∈ range p, lay (x m) ∈ Ico i0 k := fun m hm => by
      have := hlay m (Finset.mem_range.1 hm)
      exact Finset.mem_Ico.2 this
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have : ∀ i ∈ Ico i0 k, ∑ m ∈ (range p).filter (fun m => lay (x m) = i), w m =
        (((range p).filter fun m => lay (x m) = i).card : ℝ) * (d * L * c * δ i) := by
      intro i hi
      rw [Finset.sum_congr rfl (g := fun _ => (d : ℝ) * L * c * δ i)]
      · rw [Finset.sum_const, nsmul_eq_mul]
      · intro m hm
        rw [Finset.mem_filter] at hm
        simp only [hw, hm.2]
    rw [Finset.sum_congr rfl this, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_Ico.1 hi
    have h0 := hδ i hi'.1 hi'.2
    have : 0 ≤ (d : ℝ) * L * c * δ i := by positivity
    calc _ ≤ B * (d * L * c * δ i) := mul_le_mul_of_nonneg_right (hcount i) this
      _ = _ := by ring
  calc dist (ψ (x 0)) (ψ (x p)) ≤ 2 * ∑ m ∈ range p, w m := hsum2
    _ ≤ 2 * (d * L * c * B * ∑ i ∈ Ico i0 k, δ i) := by linarith
    _ = _ := by ring

end Balaban.LargeField
