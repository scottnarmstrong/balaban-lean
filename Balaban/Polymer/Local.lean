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

section Weighted

variable {κ0 κ a : P → ℝ}

omit [Fintype P] in
/-- The cluster Ursell weight vanishes for a disconnected incompatibility graph. -/
theorem aaw_eq_zero_of_not_connected {n : ℕ} (X : Fin (n + 1) → P)
    (hX : ¬ (clusterGraph inc X).Connected) : aaw inc X = 0 := by
  have : ¬ (clusterGraph inc X).Preconnected := fun hp => hX ⟨hp⟩
  unfold aaw clusterUrsell
  rw [ursell_eq_zero_of_not_preconnected this]
  simp

omit [Fintype P] [Fintype B] in
theorem term_bound (g : Finset B → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hG3 : ∀ (n : ℕ) (X : Fin (n + 1) → P), (clusterGraph inc X).Connected →
      g (unionOf supp X) ≤ ∑ i, g (supp (X i)) + c * n)
    (hκ : ∀ x, κ x = κ0 x * Real.exp (g (supp x) + c))
    (hκ0 : ∀ x, 0 ≤ κ0 x) (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ0 x) {n : ℕ} (X : Fin (n + 1) → P) :
    ‖(clusterUrsell inc X Finset.univ : ℂ) * ∏ i, K (X i)‖ * Real.exp (g (unionOf supp X)) ≤
      aaw inc X * ∏ i, κ (X i) := by
  have hF : 0 ≤ aaw inc X * ∏ i, κ (X i) := by
    refine mul_nonneg (aaw_nonneg inc X) (Finset.prod_nonneg (fun i _ => ?_))
    rw [hκ]; exact mul_nonneg (hκ0 _) (Real.exp_pos _).le
  by_cases hconn : (clusterGraph inc X).Connected
  · have h1 := hG3 n X hconn
    have hprod : ∏ i, κ (X i) = (∏ i, κ0 (X i)) * Real.exp (∑ i, g (supp (X i)) + c * (n + 1)) := by
      simp_rw [hκ, Finset.prod_mul_distrib]
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.sum_add_distrib]
      simp
      ring
    rw [norm_mul, norm_ursell_eq, norm_prod, hprod]
    have hK' : ∏ i, ‖K (X i)‖ ≤ ∏ i, κ0 (X i) :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hK _)
    have hexp : Real.exp (g (unionOf supp X)) ≤ Real.exp (∑ i, g (supp (X i)) + c * (n + 1)) :=
      Real.exp_le_exp.mpr (by nlinarith [hc])
    have ha := aaw_nonneg inc X
    calc (aaw inc X * ∏ i, ‖K (X i)‖) * Real.exp (g (unionOf supp X))
        ≤ (aaw inc X * ∏ i, κ0 (X i)) * Real.exp (∑ i, g (supp (X i)) + c * (n + 1)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hK' ha) hexp (Real.exp_pos _).le
            (mul_nonneg ha (Finset.prod_nonneg (fun i _ => hκ0 _)))
      _ = _ := by ring
  · rw [norm_mul, norm_ursell_eq, aaw_eq_zero_of_not_connected inc X hconn]
    simp

omit [Fintype B] in
theorem sum_filter_union_le {κ : P → ℝ} (hκ : ∀ x, 0 ≤ κ x) (b : B) (n : ℕ) :
    ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P)).filter (fun X => b ∈ unionOf supp X),
        aaw inc X * ∏ i, κ (X i) ≤
      ∑ X : Fin (n + 1) → P, (if ∃ i, b ∈ supp (X i) then (1 : ℝ) else 0) * aaw inc X *
        ∏ i, κ (X i) := by
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum (fun X _ => ?_)
  have hnn : 0 ≤ aaw inc X * ∏ i, κ (X i) :=
    mul_nonneg (aaw_nonneg inc X) (Finset.prod_nonneg (fun i _ => hκ _))
  by_cases hb : b ∈ unionOf supp X
  · have : ∃ i, b ∈ supp (X i) := by
      simpa only [unionOf, Finset.mem_biUnion, Finset.mem_univ, true_and] using hb
    simp only [hb, this, ite_true, one_mul]
    exact le_rfl
  · simp only [hb, ite_false]
    by_cases hex : ∃ i, b ∈ supp (X i)
    · simp only [hex, ite_true, one_mul]; exact hnn
    · simp only [hex, ite_false, zero_mul]; exact le_rfl

/-- The weighted bound for the local terms: `∑_{Y ∋ □} |P(Y)| e^{g(Y)}`. -/
theorem pe_PY_bound (g : Finset B → ℝ) (c : ℝ) (hc : 0 ≤ c) (hg : ∀ Y, 0 ≤ g Y)
    (hG3 : ∀ (n : ℕ) (X : Fin (n + 1) → P), (clusterGraph inc X).Connected →
      g (unionOf supp X) ≤ ∑ i, g (supp (X i)) + c * n)
    (hκ : ∀ x, κ x = κ0 x * Real.exp (g (supp x) + c)) (h : KPCond inc κ a)
    (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ0 x) (b : B) :
    ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY inc supp K Y‖ * Real.exp (g Y) ≤
      ∑ x, (if b ∈ supp x then κ x * Real.exp (a x) else 0) := by
  have hκ0 : ∀ x, 0 ≤ κ0 x := fun x => (norm_nonneg _).trans (hK x)
  have hKκ : ∀ x, ‖K x‖ ≤ κ x := fun x => by
    rw [hκ x]
    calc ‖K x‖ ≤ κ0 x * 1 := by rw [mul_one]; exact hK x
      _ ≤ κ0 x * Real.exp (g (supp x) + c) :=
        mul_le_mul_of_nonneg_left (Real.one_le_exp (add_nonneg (hg _) hc)) (hκ0 x)
  set R : P → Prop := fun x => b ∈ supp x with hR
  have hsum : ∀ Y : Finset B, Summable (fun n => ‖Pterm inc supp K Y n‖) := fun Y =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_Pterm_le inc supp K hKκ Y) (summable_sp inc h (fun _ => True))
  -- the bound for a fixed order `n`
  have hn : ∀ n, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
      ‖Pterm inc supp K Y n‖ * Real.exp (g Y) ≤ sp inc κ R n := by
    intro n
    have hfact : (0 : ℝ) ≤ (((n + 1).factorial : ℕ) : ℝ)⁻¹ := by positivity
    calc ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
          ‖Pterm inc supp K Y n‖ * Real.exp (g Y)
        ≤ ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
          (((n + 1).factorial : ℕ) : ℝ)⁻¹ * ∑ X ∈ ((Finset.univ : Finset (Fin (n + 1) → P)).filter
            (fun X => b ∈ unionOf supp X)).filter (fun X => unionOf supp X = Y),
              aaw inc X * ∏ i, κ (X i) := by
          refine Finset.sum_le_sum (fun Y hY => ?_)
          rw [Finset.mem_filter] at hY
          unfold Pterm
          rw [norm_mul, norm_inv, Complex.norm_natCast, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hfact
          calc ‖∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P)).filter (fun X => unionOf supp X = Y),
                (clusterUrsell inc X Finset.univ : ℂ) * ∏ i, K (X i)‖ * Real.exp (g Y)
              ≤ (∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P)).filter (fun X => unionOf supp X = Y),
                ‖(clusterUrsell inc X Finset.univ : ℂ) * ∏ i, K (X i)‖) * Real.exp (g Y) :=
                mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le
            _ = ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P)).filter (fun X => unionOf supp X = Y),
                ‖(clusterUrsell inc X Finset.univ : ℂ) * ∏ i, K (X i)‖ * Real.exp (g Y) := by
                rw [Finset.sum_mul]
            _ ≤ ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P)).filter (fun X => unionOf supp X = Y),
                aaw inc X * ∏ i, κ (X i) := by
                refine Finset.sum_le_sum (fun X hX => ?_)
                rw [Finset.mem_filter] at hX
                rw [← hX.2]
                exact term_bound inc supp g c hc hG3 hκ hκ0 K hK X
            _ = ∑ X ∈ ((Finset.univ : Finset (Fin (n + 1) → P)).filter
                  (fun X => b ∈ unionOf supp X)).filter (fun X => unionOf supp X = Y),
                aaw inc X * ∏ i, κ (X i) := by
                refine Finset.sum_congr ?_ (fun _ _ => rfl)
                ext X
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · intro hX; exact ⟨hX ▸ hY.2, hX⟩
                · intro hX; exact hX.2
      _ = (((n + 1).factorial : ℕ) : ℝ)⁻¹ * ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P)).filter
            (fun X => b ∈ unionOf supp X), aaw inc X * ∏ i, κ (X i) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin (n + 1) → P)).filter
            (fun X => b ∈ unionOf supp X)) (t := (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y))
            (g := unionOf supp) (fun X hX => by simpa using hX) _
      _ ≤ sp inc κ R n := by
          unfold sp
          refine mul_le_mul_of_nonneg_left ?_ hfact
          convert sum_filter_union_le inc supp (fun x => (norm_nonneg _).trans (hKκ x)) b n using 3
          congr 1
          by_cases hx : ∃ i, b ∈ supp (‹Fin (n + 1) → P› i) <;> simp [hR, hx]
  have h1 : ∀ Y : Finset B, ‖PY inc supp K Y‖ ≤ ∑' n, ‖Pterm inc supp K Y n‖ := fun Y =>
    norm_tsum_le_tsum_norm (hsum Y)
  have e1 : ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
      ‖PY inc supp K Y‖ * Real.exp (g Y) ≤
      ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ∑' n, (‖Pterm inc supp K Y n‖ * Real.exp (g Y)) := by
    refine Finset.sum_le_sum (fun Y _ => ?_)
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (h1 Y) (Real.exp_pos _).le
  have e2 : ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ∑' n, (‖Pterm inc supp K Y n‖ * Real.exp (g Y)) =
      ∑' n, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        (‖Pterm inc supp K Y n‖ * Real.exp (g Y)) :=
    (Summable.tsum_finsetSum (fun Y _ => (hsum Y).mul_right _)).symm
  have e3 : ∑' n, ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        (‖Pterm inc supp K Y n‖ * Real.exp (g Y)) ≤ ∑' n, sp inc κ R n := by
    refine Summable.tsum_le_tsum hn ?_ (summable_sp inc h R)
    exact summable_sum (fun Y _ => (hsum Y).mul_right _)
  refine e1.trans (e2.le.trans (e3.trans ((pe_clusterBound inc h R).2.trans (le_of_eq ?_))))
  exact Finset.sum_congr rfl (fun x _ => by by_cases hx : b ∈ supp x <;> simp [hR, hx])

end Weighted

end Balaban.Polymer
