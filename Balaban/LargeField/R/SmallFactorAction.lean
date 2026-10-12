module

public import Balaban.LargeField.LF1
public import Balaban.LargeField.R.WindowGenCompose
public import Balaban.LargeField.R.SmallFactorTilde
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lower bounds for the single-scale action and monotonicity (Lemma III.5.3, preparation)

For the single-scale generating set `singleGen` (the action `A^*_k(·; ψ_k, φ)` of (2.17′)):

* `single_gradient_bound`: a bond `{y, y'}` of the block lattice inside `X` with
  `|ψ_k(y) - ψ_k(y')| ≥ δ` costs `≥ γ₀ L^{k(d-2)} δ²/2` (LF-1 (a));
* `single_point_bound`: a block `y ⊂ X` with `φ = 1` on it costs
  `≥ γ₀ L^{k(d-2)} (|ψ_k(y)| - 1)²/2` (LF-1 (b), proved here without the condition `ψ_k(y) ≠ 0`);
* `multiAction_mono`: `β_kA^*_k(X, G; ψ, φ)` is monotone in `X` (the half bonds of P5 (1.5) make the
  action additive over disjoint domains) and non-negative.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Finset

section Single

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {Nspin : ℕ}

theorem pairSumT_nonneg {m : ℕ} (T : Finset (Torus d m))
    (f : Torus d m → EuclideanSpace ℝ (Fin Nspin)) : 0 ≤ pairSumT T f := by
  classical
  unfold pairSumT
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun y' _ => ?_)
  split_ifs
  · positivity
  · exact le_rfl

theorem le_pairSumT {m : ℕ} (T : Finset (Torus d m)) (f : Torus d m → EuclideanSpace ℝ (Fin Nspin))
    {y y' : Torus d m} (hy : y ∈ T) (hy' : y' ∈ T) (hadj : AdjT y y') :
    ‖f y - f y'‖ ^ 2 ≤ pairSumT T f := by
  classical
  have hadj' : AdjT y' y := by
    obtain ⟨hne, μ, hμ⟩ := hadj
    exact ⟨hne.symm, μ, hμ.symm⟩
  unfold pairSumT
  have hnn : ∀ u ∈ T, ∀ u' ∈ T, 0 ≤ (if AdjT u u' then ‖f u - f u'‖ ^ 2 else 0) :=
    fun u _ u' _ => by split_ifs <;> positivity
  have h1 : (if AdjT y y' then ‖f y - f y'‖ ^ 2 else 0) +
      (if AdjT y' y then ‖f y' - f y‖ ^ 2 else 0) ≤
      ∑ u ∈ T, ∑ u' ∈ T, if AdjT u u' then ‖f u - f u'‖ ^ 2 else 0 := by
    have hne : y ≠ y' := hadj.1
    calc _ = ∑ u ∈ ({y, y'} : Finset _), ∑ u' ∈ ({y, y'} : Finset _),
          (if AdjT u u' then ‖f u - f u'‖ ^ 2 else 0) := by
          rw [Finset.sum_pair hne, Finset.sum_pair hne, Finset.sum_pair hne]
          have h00 : ¬ AdjT y y := fun h => h.1 rfl
          have h11 : ¬ AdjT y' y' := fun h => h.1 rfl
          simp [h00, h11]
      _ ≤ ∑ u ∈ ({y, y'} : Finset _), ∑ u' ∈ T, (if AdjT u u' then ‖f u - f u'‖ ^ 2 else 0) := by
          refine Finset.sum_le_sum fun u hu => ?_
          have hu' : u ∈ T := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl <;> assumption
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun u' hu'' _ => hnn u hu' u' hu''
          intro u' hu''
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu''
          rcases hu'' with rfl | rfl <;> assumption
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun u hu _ =>
            Finset.sum_nonneg fun u' hu' => hnn u hu u' hu'
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl <;> assumption
  have e : ‖f y' - f y‖ = ‖f y - f y'‖ := norm_sub_rev _ _
  simp only [hadj, hadj', ite_true] at h1
  rw [e] at h1
  linarith

theorem crossSumP_nonneg (G : GeneratingSet d L N₀ k ϱ) (n : ℕ) (X : Finset (Site d L N₀ k))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin)) : 0 ≤ crossSumP G n X ψ := by
  classical
  unfold crossSumP
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- For the single-scale generating set `X ∩ Λ_n` is a union of `n`-blocks as soon as `X` is a
union of `k`-blocks. -/
theorem single_hX (hk : 1 ≤ k) {X : Finset (Site d L N₀ k)} (hXk : IsBlockUnion L N₀ k k X) :
    ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (X ∩ (singleGen d L N₀ k ϱ).layer n) := by
  intro n hn1 hnk
  by_cases hnk' : n = k
  · subst hnk'
    have : X ∩ (singleGen d L N₀ n ϱ).layer n = X := by
      ext x
      simp [GeneratingSet.layer, singleGen_Ω le_rfl, singleGen_Ω_succ]
    rw [this]; exact hXk
  · have : X ∩ (singleGen d L N₀ k ϱ).layer n = ∅ := by
      ext x
      simp [GeneratingSet.layer, singleGen_Ω hnk, singleGen_Ω (show n + 1 ≤ k by omega)]
    rw [this]
    intro x x' _
    simp

/-- **A bond violation costs** `γ₀ L^{k(d-2)} δ²/2` in the single-scale action (LF-1 (a)). -/
theorem single_gradient_bound (hk : 1 ≤ k) (hd : 2 ≤ d) (hL : 2 ≤ L) (hϱ : 2 * (d : ℝ) * L ≤ ϱ)
    {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {X : Finset (Site d L N₀ k)}
    (hXk : IsBlockUnion L N₀ k k X) (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) {y y' : Blk d L N₀ k k}
    (hy : y ∈ tBlocks d L N₀ k k X) (hy' : y' ∈ tBlocks d L N₀ k k X) (hadj : AdjT y y') :
    gamma0 d * ((L : ℝ) ^ (k * (d - 2)) / 2 * ‖ψ k y - ψ k y'‖ ^ 2) ≤
      actionG (singleGen d L N₀ k ϱ) a μ h X ψ φ := by
  refine le_trans ?_ (lf1_gradient (singleGen d L N₀ k ϱ) hd hL hϱ ha hμ h X (single_hX hk hXk) ψ φ)
  have hg : 0 ≤ gamma0 d := by unfold gamma0; positivity
  refine mul_le_mul_of_nonneg_left ?_ hg
  have hnn : ∀ n ∈ Finset.range (k + 1), 0 ≤ ((L : ℝ) ^ (n * (d - 2)) / 2) *
      pairSumT (tBlocks d L N₀ k n (lam (singleGen d L N₀ k ϱ) n ∩ X))
        (psiFull φ ψ n) := fun n _ =>
    mul_nonneg (by positivity) (pairSumT_nonneg _ _)
  have hcr : 0 ≤ ∑ n ∈ Finset.range k, ((L : ℝ) ^ ((n + 1) * (d - 2)) / 2) *
      crossSumP (singleGen d L N₀ k ϱ) n X (psiFull φ ψ) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (crossSumP_nonneg _ _ _ _)
  have h1 := Finset.single_le_sum hnn (Finset.mem_range.2 (Nat.lt_succ_self k))
  have e : tBlocks d L N₀ k k (lam (singleGen d L N₀ k ϱ) k ∩ X) = tBlocks d L N₀ k k X := by
    rw [lam_single_self hk, Finset.univ_inter]
  rw [e, psiFull_of_pos φ ψ hk] at h1
  have h2 := le_pairSumT (tBlocks d L N₀ k k X) (ψ k) hy hy' hadj
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) / 2 := by positivity
  have := mul_le_mul_of_nonneg_left h2 hL0
  linarith

/-- **A point violation costs** `γ₀ L^{k(d-2)} (|ψ_k(y)| - 1)²/2` in the single-scale action when
`φ` is a unit field on the block (LF-1 (b), without the condition `ψ_k(y) ≠ 0`). -/
theorem single_point_bound (hk : 1 ≤ k) (hd : 2 ≤ d) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a)
    {μ : ℝ} (hμ : 0 ≤ μ) (h : EuclideanSpace ℝ (Fin Nspin)) {X : Finset (Site d L N₀ k)}
    (hXk : IsBlockUnion L N₀ k k X) (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) {y : Blk d L N₀ k k}
    (hy : y ∈ tBlocks d L N₀ k k X) (hφ : ∀ x ∈ fib d L N₀ k k y, ‖φ x‖ = 1) :
    gamma0 d * ((L : ℝ) ^ (k * (d - 2)) * (1 / 2 * (‖ψ k y‖ - 1) ^ 2)) ≤
      actionG (singleGen d L N₀ k ϱ) a μ h X ψ φ := by
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  set Q := bavgL d L N₀ k k φ y with hQ
  set ε := bondE (fib d L N₀ k k y) φ with hε
  have hε0 : 0 ≤ ε := bondE_nonneg _ _
  set Lk : ℝ := (L : ℝ) ^ (k * (d - 2)) with hLk
  have hLkpos : 0 < Lk := by positivity
  set w : ℝ := ((L : ℝ) ^ k) ^ 2 * (((L : ℝ) ^ k) ^ d)⁻¹ with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hWw : Lk * w = 1 := weight_mul_c hd hL0 k
  have hcast : ((L ^ k : ℕ) : ℝ) = (L : ℝ) ^ k := by push_cast; ring
  have h1 : 1 - ‖Q‖ ^ 2 ≤ (w * ε) / 2 := by
    have := hardSpin_one_sub_sq_le (sideEq (L := L) (N₀ := N₀) (le_refl k)) φ y
      (fun x hx => hφ x (by rw [fib_eq_blockFibre]; exact hx))
    rw [← fib_eq_blockFibre, hcast] at this
    rw [hQ, bavgL_eq, hε, hw]
    linarith
  have hQ1 : ‖Q‖ ≤ 1 := norm_bavg_le_one le_rfl φ y hφ
  set Δ := ‖ψ k y - Q‖ ^ 2 with hΔ
  set P := (‖ψ k y‖ - 1) ^ 2 with hP
  have hQ0 : 0 ≤ ‖Q‖ := norm_nonneg _
  have hP1 : P ≤ 2 * Δ + 2 * (1 - ‖Q‖ ^ 2) := by
    have h2 : |‖ψ k y‖ - ‖Q‖| ≤ ‖ψ k y - Q‖ := abs_norm_sub_norm_le _ _
    have ha2 : (‖ψ k y‖ - ‖Q‖) ^ 2 ≤ Δ := by
      calc (‖ψ k y‖ - ‖Q‖) ^ 2 = |‖ψ k y‖ - ‖Q‖| ^ 2 := (sq_abs _).symm
        _ ≤ ‖ψ k y - Q‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    have hb : (1 - ‖Q‖) ^ 2 ≤ 1 - ‖Q‖ ^ 2 := by nlinarith
    have : P = ((‖ψ k y‖ - ‖Q‖) - (1 - ‖Q‖)) ^ 2 := by rw [hP]; ring
    rw [this]
    nlinarith [sq_nonneg ((‖ψ k y‖ - ‖Q‖) + (1 - ‖Q‖))]
  -- lower bound for the action
  have hak := (ha k hk le_rfl).1
  have hsingle := actionG_single (ϱ := ϱ) hk a μ h X ψ φ
  have hblock : a k * Lk * Δ ≤ ∑ y' ∈ tBlocks d L N₀ k k X,
      a k * Lk * ‖ψ k y' - bavgL d L N₀ k k φ y'‖ ^ 2 :=
    Finset.single_le_sum (f := fun y' => a k * Lk * ‖ψ k y' - bavgL d L N₀ k k φ y'‖ ^ 2)
      (fun y' _ => by positivity) hy
  have hbond : ε ≤ bondE X φ := bondE_mono (fib_subset_of_mem_tBlocks hXk hy) φ
  have hmass : 0 ≤ μ / 2 * ∑ x ∈ X, ‖φ x - h‖ ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  have hact : 1 / 4 * (Lk * Δ) + 1 / 2 * ε ≤ actionG (singleGen d L N₀ k ϱ) a μ h X ψ φ := by
    rw [hsingle]
    have hΔ0 : 0 ≤ Δ := by positivity
    have : 1 / 4 * (Lk * Δ) ≤ 1 / 2 * (a k * Lk * Δ) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (show (1 / 2 : ℝ) ≤ a k from (ha k hk le_rfl).1) hLkpos.le) hΔ0
      linarith
    linarith
  have hr : Lk * (1 - ‖Q‖ ^ 2) ≤ ε / 2 := by
    calc Lk * (1 - ‖Q‖ ^ 2) ≤ Lk * ((w * ε) / 2) := mul_le_mul_of_nonneg_left h1 hLkpos.le
      _ = (Lk * w) * ε / 2 := by ring
      _ = ε / 2 := by rw [hWw]; ring
  have hg : gamma0 d ≤ 1 / 4 := by
    unfold gamma0
    have : (4 : ℝ) ≤ 28 * d := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hPnn : 0 ≤ Lk * (1 / 2 * P) := by positivity
  have hkey : Lk * (1 / 2 * P) ≤ Lk * Δ + ε / 2 := by nlinarith
  calc gamma0 d * (Lk * (1 / 2 * P)) ≤ 1 / 4 * (Lk * (1 / 2 * P)) :=
        mul_le_mul_of_nonneg_right hg hPnn
    _ ≤ 1 / 4 * (Lk * Δ + ε / 2) := by linarith
    _ ≤ _ := by linarith

end Single

section Mono

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {Nspin : ℕ}

/-- The bond part `½ E(X) + ¼ E(st X)` of `A + ¼ ∑_{st}` is monotone in `X`
(a bond is weighted `½` if both end points lie in `X`, `¼` if exactly one does). -/
theorem bond_star_mono {ℓ : ℕ} [NeZero ℓ] {X X' : Finset (Torus d ℓ)} (hXX : X ⊆ X')
    (φ : Torus d ℓ → EuclideanSpace ℝ (Fin Nspin)) :
    1 / 2 * bondE X φ + 1 / 4 * starBondE X φ ≤ 1 / 2 * bondE X' φ + 1 / 4 * starBondE X' φ := by
  classical
  unfold bondE starBondE bondEdir
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun μ _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  have hnn := bondTerm_nonneg φ μ x
  by_cases h1 : x ∈ X <;> by_cases h2 : x + Pi.single μ 1 ∈ X <;>
    by_cases h3 : x ∈ X' <;> by_cases h4 : x + Pi.single μ 1 ∈ X' <;>
    simp [h1, h2, h3, h4]
  all_goals first
    | linarith
    | (exfalso; first | exact h3 (hXX h1) | exact h4 (hXX h2))

theorem compWeight_nonneg {L : ℕ} (hL : 2 ≤ L) {a₁ : ℝ} (ha : 0 < a₁) (r : ℕ) :
    0 ≤ compWeight L a₁ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · unfold compWeight
    simp
  · exact (compWeight_pos hL ha hr).le

/-- `β_kA^*_k(X, G; ψ, φ)` is monotone in `X` for non-negative weights, mass and coupling. -/
theorem multiAction_mono (G : GeneratingSet d L N₀ k ϱ) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {μ : ℝ}
    (hμ : 0 ≤ μ) {βk : ℝ} (hβ : 0 ≤ βk) (h : EuclideanSpace ℝ (Fin Nspin))
    {X X' : Finset (Site d L N₀ k)} (hXX : X ⊆ X')
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) :
    multiAction G a βk μ h X ψ φ ≤ multiAction G a βk μ h X' ψ φ := by
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact_mod_cast this
  have hβ0 : 0 ≤ betaCanon d L βk k 0 := by
    unfold betaCanon; positivity
  unfold multiAction
  refine mul_le_mul_of_nonneg_left ?_ hβ0
  unfold actionG
  have h1 : ∑ n ∈ Finset.Icc 1 k, ∑ y ∈ tBlocks d L N₀ k n (lam G n ∩ X),
        a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ k n φ y‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 k, ∑ y ∈ tBlocks d L N₀ k n (lam G n ∩ X'),
        a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ k n φ y‖ ^ 2 := by
    refine Finset.sum_le_sum fun n _ => ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ => by
      have := ha n
      positivity
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_tBlocks.1 hy
    exact mem_tBlocks.2 ⟨x, Finset.inter_subset_inter_left hXX hx, rfl⟩
  have h2 : ∑ x ∈ X, ‖φ x - h‖ ^ 2 ≤ ∑ x ∈ X', ‖φ x - h‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hXX fun _ _ _ => by positivity
  have h3 := bond_star_mono hXX φ
  have h4 : μ / 2 * ∑ x ∈ X, ‖φ x - h‖ ^ 2 ≤ μ / 2 * ∑ x ∈ X', ‖φ x - h‖ ^ 2 :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

theorem multiAction_nonneg (G : GeneratingSet d L N₀ k ϱ) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {μ : ℝ}
    (hμ : 0 ≤ μ) {βk : ℝ} (hβ : 0 ≤ βk) (h : EuclideanSpace ℝ (Fin Nspin))
    (X : Finset (Site d L N₀ k)) (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) :
    0 ≤ multiAction G a βk μ h X ψ φ := by
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact_mod_cast this
  have hβ0 : 0 ≤ betaCanon d L βk k 0 := by
    unfold betaCanon; positivity
  unfold multiAction
  exact mul_nonneg hβ0 (add_nonneg (actionG_nonneg G ha hμ h X ψ φ)
    (mul_nonneg (by norm_num) (starBondE_nonneg X φ)))

end Mono

section Violation

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {Nspin : ℕ}

/-- **A violation of `Ψ̃` costs** `γ₀ L^{k(d-2)} θ²/2` in the single-scale action, for a unit field
`φ` on `X`: if `ψ_k ∉ Ψ̃(T; θ)` for the set `T` of blocks contained in `X`, either a bond of
nearest-neighbour blocks has `|ψ_k(y) - ψ_k(y')| ≥ θ` (LF-1 (a)) or a block has
`||ψ_k(y)| - 1| ≥ θ` (LF-1 (b)). -/
theorem single_violation_bound (hk : 1 ≤ k) (hd : 2 ≤ d) (hL : 2 ≤ L)
    (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {X : Finset (Site d L N₀ k)}
    (hXk : IsBlockUnion L N₀ k k X) (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) (hφ : ∀ x ∈ X, ‖φ x‖ = 1) {θ : ℝ}
    (hθ : 0 ≤ θ) (hviol : ¬ PsiTildeSet {y : Blk d L N₀ k k | fib d L N₀ k k y ⊆ X} (ψ k) θ) :
    gamma0 d * ((L : ℝ) ^ (k * (d - 2)) * (θ ^ 2 / 2)) ≤
      actionG (singleGen d L N₀ k ϱ) a μ h X ψ φ := by
  have hg0 : 0 ≤ gamma0 d := by unfold gamma0; positivity
  have hmem : ∀ y : Blk d L N₀ k k, fib d L N₀ k k y ⊆ X → y ∈ tBlocks d L N₀ k k X := fun y hy =>
    (mem_tBlocks_iff_fib_subset hXk le_rfl).2 hy
  unfold PsiTildeSet at hviol
  rw [not_and_or] at hviol
  rcases hviol with hb | hp
  · push Not at hb
    obtain ⟨y, hy, y', hy', hadj, hbig⟩ := hb
    have := single_gradient_bound hk hd hL hϱ ha hμ h hXk ψ φ (hmem y hy) (hmem y' hy') hadj
    refine le_trans ?_ this
    have h9 : θ ^ 2 ≤ ‖ψ k y - ψ k y'‖ ^ 2 := pow_le_pow_left₀ hθ hbig 2
    have := mul_le_mul_of_nonneg_left h9 (by positivity : 0 ≤ (L : ℝ) ^ (k * (d - 2)) / 2)
    exact mul_le_mul_of_nonneg_left (by nlinarith) hg0
  · push Not at hp
    obtain ⟨y, hy, hbig⟩ := hp
    have := single_point_bound (ϱ := ϱ) hk hd ha hμ h hXk ψ φ (hmem y hy)
      (fun x hx => hφ x (hy hx))
    refine le_trans ?_ this
    have h9 : θ ^ 2 ≤ (‖ψ k y‖ - 1) ^ 2 := by
      have : θ ^ 2 ≤ |‖ψ k y‖ - 1| ^ 2 := pow_le_pow_left₀ hθ hbig 2
      rwa [sq_abs] at this
    have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := by positivity
    exact mul_le_mul_of_nonneg_left (by nlinarith) hg0

/-- **The single-scale small factor** (Lemma III.5.3 (e), `ϰ₅`, level-torus form): a violation of
`Ψ̃(·; θ)` on `X` costs `β_kA^*_k(X; ψ_k, φ) ≥ ½ γ₀ β_k θ²` (with `θ = δ_k/(6K₁)` this is
`γ₅ = γ₀ β_k δ_k²/(72 K₁²)`). -/
theorem single_smallFactor (hk : 1 ≤ k) (hd : 2 ≤ d) (hL : 2 ≤ L)
    (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {X : Finset (Site d L N₀ k)}
    (hXk : IsBlockUnion L N₀ k k X) (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) (hφ : ∀ x ∈ X, ‖φ x‖ = 1) {βk : ℝ}
    (hβ : 0 ≤ βk) {θ : ℝ} (hθ : 0 ≤ θ)
    (hviol : ¬ PsiTildeSet {y : Blk d L N₀ k k | fib d L N₀ k k y ⊆ X} (ψ k) θ) :
    1 / 2 * gamma0 d * (βk * θ ^ 2) ≤ multiAction (singleGen d L N₀ k ϱ) a βk μ h X ψ φ := by
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact_mod_cast this
  have hβ0def : betaCanon d L βk k 0 = βk / (L : ℝ) ^ (k * (d - 2)) := by
    unfold betaCanon; simp
  have hβ0 : 0 ≤ betaCanon d L βk k 0 := by rw [hβ0def]; positivity
  have hβk : βk = betaCanon d L βk k 0 * (L : ℝ) ^ (k * (d - 2)) := by
    have : (L : ℝ) ^ (k * (d - 2)) ≠ 0 := pow_ne_zero _ hLpos.ne'
    rw [hβ0def]; field_simp
  have h1 := single_violation_bound hk hd hL hϱ ha hμ h hXk ψ φ hφ hθ hviol
  have h2 := bondE_nonneg X φ
  have h3 := starBondE_nonneg X φ
  unfold multiAction
  have h4 := mul_le_mul_of_nonneg_left h1 hβ0
  have h5 : betaCanon d L βk k 0 * actionG (singleGen d L N₀ k ϱ) a μ h X ψ φ ≤
      betaCanon d L βk k 0 * (actionG (singleGen d L N₀ k ϱ) a μ h X ψ φ +
        1 / 4 * starBondE X φ) := mul_le_mul_of_nonneg_left (by linarith) hβ0
  have e : 1 / 2 * gamma0 d * (βk * θ ^ 2) =
      betaCanon d L βk k 0 * (gamma0 d * ((L : ℝ) ^ (k * (d - 2)) * (θ ^ 2 / 2))) := by
    conv_lhs => rw [hβk]
    ring
  linarith

end Violation

end Balaban.LargeField
