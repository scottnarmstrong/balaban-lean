module

public import Balaban.LargeField.LF1
public import Balaban.LargeField.LF1.Violation
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
  have hlam : lam (singleGen d L N₀ k ϱ) k = Finset.univ := lam_single_self hk
  have hmem : ∀ z : Blk d L N₀ k k, z ∈ tBlocks d L N₀ k k X →
      z ∈ tBlocks d L N₀ k k (lam (singleGen d L N₀ k ϱ) k ∩ X) := fun z hz => by
    rwa [hlam, Finset.univ_inter]
  exact lf1_pair_gain (singleGen d L N₀ k ϱ) hk hd hL hϱ ha hμ h (single_hX hk hXk) ψ φ
    (hmem y hy) (hmem y' hy') hadj

/-- **A point violation costs** `γ₀ L^{k(d-2)} (|ψ_k(y)| - 1)²/2` in the single-scale action when
`φ` is a unit field on the block (LF-1 (b), without the condition `ψ_k(y) ≠ 0`). -/
theorem single_point_bound (hk : 1 ≤ k) (hd : 2 ≤ d) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a)
    {μ : ℝ} (hμ : 0 ≤ μ) (h : EuclideanSpace ℝ (Fin Nspin)) {X : Finset (Site d L N₀ k)}
    (hXk : IsBlockUnion L N₀ k k X) (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) {y : Blk d L N₀ k k}
    (hy : y ∈ tBlocks d L N₀ k k X) (hφ : ∀ x ∈ fib d L N₀ k k y, ‖φ x‖ = 1) :
    gamma0 d * ((L : ℝ) ^ (k * (d - 2)) * (1 / 2 * (‖ψ k y‖ - 1) ^ 2)) ≤
      actionG (singleGen d L N₀ k ϱ) a μ h X ψ φ := by
  have hlam : lam (singleGen d L N₀ k ϱ) k = Finset.univ := lam_single_self hk
  exact lf1_point_gain (singleGen d L N₀ k ϱ) hk hd ha hμ h (single_hX hk hXk) ψ φ
    (by rwa [hlam, Finset.univ_inter]) hφ

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
  have hlam : lam (singleGen d L N₀ k ϱ) k = Finset.univ := lam_single_self hk
  exact lf1_violation_gain (singleGen d L N₀ k ϱ) hk hd hL hϱ ha hμ h (single_hX hk hXk)
    (by rw [hlam, Finset.univ_inter]) ψ φ hφ hθ hviol

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
