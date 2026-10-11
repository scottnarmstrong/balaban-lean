module

public import Balaban.Polymer.PE

/-!
# Local decomposition of the cluster sum

Polymers have supports `supp P ⊆ B` in a finite set of blocks.  Grouping clusters by the union of
their supports gives `logSeries K = ∑_Y P(Y)` (`logSeries_eq_sum_PY`), where `P(Y)` depends only
on the activities of the polymers supported in `Y` (`PY_congr`), vanishes unless `Y` is the union
of a cluster with connected incompatibility graph, and satisfies the weighted bound
`pe_PY_bound`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

variable {P : Type*} [Fintype P] (inc : P → P → Prop) {B : Type*} [Fintype B] (supp : P → Finset B)

/-- The union of the supports of the members of a cluster. -/
def unionOf {n : ℕ} (X : Fin n → P) : Finset B := Finset.univ.biUnion (fun i => supp (X i))

/-- The contribution of the clusters of order `n+1` with union `Y`. -/
def Pterm (K : P → ℂ) (Y : Finset B) (n : ℕ) : ℂ :=
  (((n + 1).factorial : ℕ) : ℂ)⁻¹ *
    ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P)).filter (fun X => unionOf supp X = Y),
      (clusterUrsell inc X Finset.univ : ℂ) * ∏ i, K (X i)

/-- The local term `P(Y)` of the cluster sum. -/
def PY (K : P → ℂ) (Y : Finset B) : ℂ := ∑' n, Pterm inc supp K Y n

theorem clTerm_eq_sum_Pterm (K : P → ℂ) (n : ℕ) :
    clTerm inc K n = ∑ Y : Finset B, Pterm inc supp K Y n := by
  unfold clTerm Pterm
  rw [← Finset.mul_sum]
  congr 1
  exact (Finset.sum_fiberwise (Finset.univ : Finset (Fin (n + 1) → P)) (unionOf supp)
    (fun X => (clusterUrsell inc X Finset.univ : ℂ) * ∏ i, K (X i))).symm

omit [Fintype B] in
theorem norm_Pterm_le {κ : P → ℝ} (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x) (Y : Finset B) (n : ℕ) :
    ‖Pterm inc supp K Y n‖ ≤ sp inc κ (fun _ => True) n := by
  unfold Pterm sp
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hex : (∃ i : Fin (n + 1), True) := ⟨0, trivial⟩
  simp only [hex, ite_true, one_mul]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P)).filter (fun X => unionOf supp X = Y),
        ‖(clusterUrsell inc X Finset.univ : ℂ) * ∏ i, K (X i)‖
      ≤ ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P)).filter (fun X => unionOf supp X = Y),
        aaw inc X * ∏ i, κ (X i) := by
        refine Finset.sum_le_sum (fun X _ => ?_)
        rw [norm_mul, norm_ursell_eq, norm_prod]
        exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
          (fun i _ => hK _)) (aaw_nonneg inc X)
    _ ≤ ∑ X : Fin (n + 1) → P, aaw inc X * ∏ i, κ (X i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun X _ _ =>
          mul_nonneg (aaw_nonneg inc X) (Finset.prod_nonneg (fun i _ =>
            (norm_nonneg _).trans (hK (X i)))))

theorem logSeries_eq_sum_PY {κ a : P → ℝ} (h : KPCond inc κ a) (K : P → ℂ)
    (hK : ∀ x, ‖K x‖ ≤ κ x) :
    logSeries inc K = ∑ Y : Finset B, PY inc supp K Y := by
  have hs : ∀ Y : Finset B, Summable (fun n => Pterm inc supp K Y n) := fun Y =>
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_Pterm_le inc supp K hK Y) (summable_sp inc h (fun _ => True)))
  unfold logSeries PY
  simp_rw [clTerm_eq_sum_Pterm inc supp]
  exact Summable.tsum_finsetSum (fun Y _ => hs Y)

omit [Fintype B] in
/-- Locality: `P(Y)` only depends on the activities of polymers supported inside `Y`. -/
theorem PY_congr {K K' : P → ℂ} (Y : Finset B) (hKK : ∀ x, supp x ⊆ Y → K x = K' x) :
    PY inc supp K Y = PY inc supp K' Y := by
  unfold PY
  refine tsum_congr (fun n => ?_)
  unfold Pterm
  congr 1
  refine Finset.sum_congr rfl (fun X hX => ?_)
  rw [Finset.mem_filter] at hX
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  apply hKK
  rw [← hX.2]
  exact Finset.subset_biUnion_of_mem (fun i => supp (X i)) (Finset.mem_univ i)

end Balaban.Polymer
