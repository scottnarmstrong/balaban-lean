module

public import Balaban.LargeField.R.WindowGenSingle
public import Balaban.LargeField.R.WindowGenCS
public import Balaban.LargeField.Analytic.Constants
public import Balaban.Multiscale.Operator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The composed Gaussian dominates the single-scale action (Lemma III.2.3, (2.17′))

The data of the composed kernel (III.1.4) on a `k`-block `z ⊂ Ω^c_k` with leaves `x ⊂ z`
(`leaf`), written as sums over the sites of `z` (a leaf `x` of layer `n_x` has `L^{n_x d}` sites,
the weight `w_x = L^{(n_x - k)d}` of a leaf is the fraction of the sites of `z` it contains):

* `compMean G ϖ ψ z = 𝒬^♮_z ψ^G = ∑_{x ⊂ z} w_x ϖ_{n_x} ψ^G(x)` (the mean; `ϖ ≡ 1` is the ideal one);
* `compWeightZ G L a₁ z = a_z`, `a_z⁻¹ = ∑_{x ⊂ z} w_x u_{k - n_x}`, `u_r = 1/a_r` (the ideal
  weight of BG (6.5), `a_r = compWeight L a₁ r`);
* `varsigmaBar G ϖ z = ς̄_z = ∑_{x ⊂ z} w_x |ϖ_{n_x} - 1|`;
* `composedGauss G βk aN ϖ ψ X = 𝒢^♮ = ∑_{z ⊂ X} ½ β_k a^♮_z |ψ_k(z) - 𝒬^♮_z ψ^G|²`.

`composed_dominates` is (2.17′).  The actual composed weights `a^♮_z = a_z(1 + η_z)`,
`|η_z| ≤ η`, are data subject to (III.1.6); the premises are the error bounds (III.1.6),
(III.1.7) (`varsigmaBar`) and the count of the `k`-blocks of `X` (Lemma III.1.2 (d)).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Finset

section Defs

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {Nspin : ℕ}

/-- `V = L^{kd}`: the number of sites of a `k`-block, as a real number. -/
noncomputable def blockVol (d L k : ℕ) : ℝ := ((L : ℝ) ^ k) ^ d

/-- The composed mean `𝒬^♮_z ψ^G = V⁻¹ ∑_{s ∈ z} ϖ_{n_s} ψ^G(s)`. -/
noncomputable def compMean (G : GeneratingSet d L N₀ k ϱ) (ϖ : ℕ → ℝ)
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin)) (z : Blk d L N₀ k k) :
    EuclideanSpace ℝ (Fin Nspin) :=
  (blockVol d L k)⁻¹ • ∑ s ∈ fib d L N₀ k k z, ϖ (G.layerIndex s) • leafField G ψ s

/-- The ideal composed weight `a_z`, `a_z⁻¹ = V⁻¹ ∑_{s ∈ z} u_{k - n_s}`. -/
noncomputable def compWeightZ (G : GeneratingSet d L N₀ k ϱ) (a₁ : ℝ) (z : Blk d L N₀ k k) : ℝ :=
  ((blockVol d L k)⁻¹ *
    ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹)⁻¹

/-- `ς̄_z = V⁻¹ ∑_{s ∈ z} |ϖ_{n_s} - 1|`. -/
noncomputable def varsigmaBar (G : GeneratingSet d L N₀ k ϱ) (ϖ : ℕ → ℝ) (z : Blk d L N₀ k k) : ℝ :=
  (blockVol d L k)⁻¹ * ∑ s ∈ fib d L N₀ k k z, |ϖ (G.layerIndex s) - 1|

/-- `𝒢^♮ = ∑_{z ⊂ X} ½ β_k a^♮_z |ψ_k(z) - 𝒬^♮_z ψ^G|²`. -/
noncomputable def composedGauss (G : GeneratingSet d L N₀ k ϱ) (βk : ℝ) (aN : Blk d L N₀ k k → ℝ)
    (ϖ : ℕ → ℝ) (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (X : Finset (Site d L N₀ k)) : ℝ :=
  ∑ z ∈ tBlocks d L N₀ k k X, 1 / 2 * βk * aN z * ‖ψ k z - compMean G ϖ ψ z‖ ^ 2

/-- `β_kA^*_k(X, G; ψ, φ) = β^{(k)}_0 (A_G(X; ψ, φ) + ¼ ∑_{b ∈ st(X)} |∂φ(b)|²)` (P5 (1.5)). -/
noncomputable def multiAction (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (βk μ : ℝ)
    (h : EuclideanSpace ℝ (Fin Nspin)) (X : Finset (Site d L N₀ k))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) : ℝ :=
  betaCanon d L βk k 0 * (actionG G a μ h X ψ φ + 1 / 4 * starBondE X φ)

end Defs

section Block

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {Nspin : ℕ}
  (G : GeneratingSet d L N₀ k ϱ) {X : Finset (Site d L N₀ k)}

theorem blockVol_eq (d L k : ℕ) : blockVol d L k = (((L ^ k : ℕ) : ℝ)) ^ d := by
  unfold blockVol; push_cast; rfl

/-- The sites of `X ⊂ Ω₁ ∖ Ω_k` lie in layers `1 ≤ n < k`. -/
theorem layerIndex_range (hXΩ : ∀ s ∈ X, s ∈ G.Ω 1 ∧ s ∉ G.Ω k) {s : Site d L N₀ k} (hs : s ∈ X) :
    1 ≤ G.layerIndex s ∧ G.layerIndex s < k := by
  obtain ⟨h1, h2, h3⟩ := G.layerIndex_spec (hXΩ s hs).1
  refine ⟨h1, lt_of_le_of_ne h2 fun h => (hXΩ s hs).2 ?_⟩
  rw [h] at h3
  exact (G.mem_layer.1 h3).1

/-- `(Q_k φ)(z) = V⁻¹ ∑_{s ∈ z} (Q_{n_s} φ)(s)`: the block average is the average of the leaf
averages (the leaves of `z` partition `z`). -/
theorem bavg_block (hX : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (X ∩ G.layer n))
    (hXΩ : ∀ s ∈ X, s ∈ G.Ω 1 ∧ s ∉ G.Ω k) {z : Blk d L N₀ k k}
    (hz : fib d L N₀ k k z ⊆ X) (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) :
    bavgL d L N₀ k k φ z = (blockVol d L k)⁻¹ • ∑ s ∈ fib d L N₀ k k z, leafAvg G φ s := by
  have ha : ∀ s ∈ fib d L N₀ k k z, s ∈ leaf G s := fun s _ => mem_leaf_self G s
  have hb : ∀ s ∈ fib d L N₀ k k z, ∀ s' ∈ leaf G s,
      s' ∈ fib d L N₀ k k z ∧ leaf G s' = leaf G s := by
    intro s hs s' hs'
    obtain ⟨-, -, -, hl⟩ := leaf_closed G hX (hz hs) (hXΩ s (hz hs)).1 hs'
    refine ⟨?_, hl⟩
    rw [mem_fib] at hs ⊢
    rw [blkMap_of_mem_leaf G (layerIndex_le G s) le_rfl hs', hs]
  have hpart := sum_partition_avg (fib d L N₀ k k z) (leaf G) ha hb φ
  have e : ∀ s ∈ fib d L N₀ k k z, ((leaf G s).card : ℝ)⁻¹ • ∑ s' ∈ leaf G s, φ s' =
      leafAvg G φ s := by
    intro s _
    unfold leafAvg bavgL bavg
    rw [← fib_eq_blockFibre, card_leaf]
    push_cast
    rfl
  rw [Finset.sum_congr rfl e] at hpart
  rw [hpart, blockVol_eq]
  unfold bavgL bavg
  rw [← fib_eq_blockFibre]

end Block

section BlockActual

variable {α : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem sq_norm_le_two (t sh : E) : ‖t‖ ^ 2 ≤ 2 * ‖t - sh‖ ^ 2 + 2 * ‖sh‖ ^ 2 := by
  have h : ‖t‖ ≤ ‖t - sh‖ + ‖sh‖ := by
    calc ‖t‖ = ‖(t - sh) + sh‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  nlinarith [norm_nonneg (t - sh), norm_nonneg sh, norm_nonneg t, sq_nonneg (‖t - sh‖ - ‖sh‖)]

/-- The real-number core of the block inequality with the actual composed weight. -/
theorem actual_core {β0 Lk aN aZ η B2 X0 Y Z T Q ak : ℝ} (hβ0 : 0 ≤ β0) (hLk : 0 < Lk)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (haZ : 0 < aZ) (haN1 : (1 - η) * aZ ≤ aN) (haN2 : aN ≤ 3)
    (hT : 0 ≤ T) (hX0 : 0 ≤ X0) (hsq : X0 ≤ 2 * Y + 2 * Z) (hZB : Z ≤ B2)
    (hZ0 : 0 ≤ Z) (hQb : ak * Lk * Q ≤ aZ * Lk * X0 + T) :
    1 / 2 * (1 - η) * (β0 * (1 / 2 * (ak * Lk * Q))) ≤
      1 / 2 * (β0 * Lk) * aN * Y + β0 * (1 / 2 * T) + 3 / 2 * (β0 * Lk) * B2 := by
  have hb : 0 ≤ β0 * Lk := mul_nonneg hβ0 hLk.le
  have haNpos : 0 ≤ aN := by nlinarith
  -- composed term
  have e1 : 1 / 2 * (β0 * Lk) * aN * (1 / 2 * X0 - Z) ≤ 1 / 2 * (β0 * Lk) * aN * Y := by
    have : 0 ≤ 1 / 2 * (β0 * Lk) * aN := by positivity
    have h : 1 / 2 * X0 - Z ≤ Y := by linarith
    exact mul_le_mul_of_nonneg_left h this
  have e3 : 1 / 4 * (β0 * Lk) * ((1 - η) * aZ) * X0 ≤ 1 / 4 * (β0 * Lk) * aN * X0 := by
    have : 0 ≤ 1 / 4 * (β0 * Lk) * X0 := by positivity
    have h := mul_le_mul_of_nonneg_left haN1 this
    linarith
  have e4 : 1 / 2 * (β0 * Lk) * aN * Z ≤ 3 / 2 * (β0 * Lk) * B2 := by
    have h5 : aN * Z ≤ 3 * B2 := by
      calc aN * Z ≤ 3 * Z := mul_le_mul_of_nonneg_right haN2 hZ0
        _ ≤ 3 * B2 := by linarith
    have := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 1 / 2 * (β0 * Lk))
    linarith
  have e2 : 1 / 2 * (β0 * Lk) * aN * (1 / 2 * X0 - Z) =
      1 / 4 * (β0 * Lk) * aN * X0 - 1 / 2 * (β0 * Lk) * aN * Z := by ring
  have h6 : 1 / 2 * (1 - η) * (β0 * (1 / 2 * (ak * Lk * Q))) ≤
      1 / 2 * (1 - η) * (β0 * (1 / 2 * (aZ * Lk * X0 + T))) := by
    have : 0 ≤ 1 / 2 * (1 - η) * β0 := by
      have : 0 ≤ 1 - η := by linarith
      positivity
    have h := mul_le_mul_of_nonneg_left hQb (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h' := mul_le_mul_of_nonneg_left h this
    nlinarith
  have h7 : 1 / 2 * (1 - η) * (β0 * (1 / 2 * (aZ * Lk * X0 + T))) ≤
      1 / 4 * (β0 * Lk) * ((1 - η) * aZ) * X0 + β0 * (1 / 2 * T) := by
    have hb' : 0 ≤ β0 * T := mul_nonneg hβ0 hT
    nlinarith
  linarith

/-- The block inequality with the actual composed weight and mean. -/
theorem block_dominates_actual {k d L : ℕ} (hL : 2 ≤ L) (hd : 2 ≤ d) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (S : Finset α) (nS : α → ℕ) {V : ℝ} (hV : (S.card : ℝ) = V) (hVd : V = ((L : ℝ) ^ k) ^ d)
    (hn : ∀ s ∈ S, 1 ≤ nS s ∧ nS s < k) {aZ : ℝ}
    (haZ : aZ⁻¹ = V⁻¹ * ∑ s ∈ S, (compWeight L a₁ (k - nS s))⁻¹) (haZ2 : aZ ≤ 2)
    {aN η β0 B : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (haN : |aN - aZ| ≤ η * aZ) (hβ0 : 0 ≤ β0)
    (t0 sh : E) (hsh : ‖sh‖ ≤ B) (τ : α → E) :
    1 / 2 * (1 - η) * (β0 * (1 / 2 * (compWeight L a₁ k * (L : ℝ) ^ (k * (d - 2)) *
        ‖t0 + V⁻¹ • ∑ s ∈ S, τ s‖ ^ 2))) ≤
      1 / 2 * (β0 * (L : ℝ) ^ (k * (d - 2))) * aN * ‖t0 - sh‖ ^ 2 +
        β0 * (1 / 2 * ∑ s ∈ S, compWeight L a₁ (nS s) / ((L : ℝ) ^ nS s) ^ 2 * ‖τ s‖ ^ 2) +
        3 / 2 * (β0 * (L : ℝ) ^ (k * (d - 2))) * B ^ 2 := by
  have hdom := block_dominates hL hd ha₁ S nS hV hVd hn haZ t0 τ
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hLk : 0 < (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hVpos : 0 < V := by
    rw [hVd]; positivity
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < S.card := by rw [hV]; exact hVpos
    exact_mod_cast this
  have hapos : ∀ r, 1 ≤ r → 0 < compWeight L a₁ r := fun r hr => compWeight_pos hL ha₁ hr
  have hsum_pos : 0 < ∑ s ∈ S, (compWeight L a₁ (k - nS s))⁻¹ :=
    Finset.sum_pos (fun s hs => inv_pos.2 (hapos _ (by have := hn s hs; omega))) hSne
  have haZpos : 0 < aZ := by
    have : 0 < aZ⁻¹ := by rw [haZ]; positivity
    exact inv_pos.1 this
  have hc : ∀ s ∈ S, 0 ≤ compWeight L a₁ (nS s) / ((L : ℝ) ^ nS s) ^ 2 * ‖τ s‖ ^ 2 := fun s hs =>
    mul_nonneg (div_nonneg (hapos _ (hn s hs).1).le (by positivity)) (by positivity)
  have hT : 0 ≤ ∑ s ∈ S, compWeight L a₁ (nS s) / ((L : ℝ) ^ nS s) ^ 2 * ‖τ s‖ ^ 2 :=
    Finset.sum_nonneg hc
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hsh
  have hshsq : ‖sh‖ ^ 2 ≤ B ^ 2 := by gcongr
  obtain ⟨haN1, haN2⟩ := abs_le.1 haN
  have haN_lo : (1 - η) * aZ ≤ aN := by nlinarith
  have haN_hi : aN ≤ 3 := by nlinarith
  exact actual_core hβ0 hLk hη0 hη haZpos haN_lo haN_hi hT (by positivity)
    (sq_norm_le_two t0 sh) hshsq (by positivity) hdom

end BlockActual

section Global

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {Nspin : ℕ}

/-- The inequality of Lemma III.2.3 on one `k`-block `z ⊂ X`. -/
theorem block_final (G : GeneratingSet d L N₀ k ϱ) {X : Finset (Site d L N₀ k)} (hL : 2 ≤ L)
    (hd : 2 ≤ d) {a₁ : ℝ} (ha₁ : 0 < a₁) (hadm : IsAdmissibleWeights k (compWeight L a₁))
    (hX : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (X ∩ G.layer n))
    (hXΩ : ∀ s ∈ X, s ∈ G.Ω 1 ∧ s ∉ G.Ω k) {z : Blk d L N₀ k k} (hz : fib d L N₀ k k z ⊆ X)
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) {βk : ℝ} (hβ : 0 ≤ βk) (ϖ : ℕ → ℝ)
    {aN η Mψ : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (haN : |aN - compWeightZ G a₁ z| ≤ η * compWeightZ G a₁ z)
    (hM : ∀ s ∈ X, ‖leafField G ψ s‖ ≤ Mψ) :
    1 / 2 * (1 - η) * (betaCanon d L βk k 0 * (1 / 2 * (compWeight L a₁ k *
        (L : ℝ) ^ (k * (d - 2)) * ‖ψ k z - bavgL d L N₀ k k φ z‖ ^ 2))) ≤
      1 / 2 * βk * aN * ‖ψ k z - compMean G ϖ ψ z‖ ^ 2 +
        betaCanon d L βk k 0 * (1 / 2 * ∑ s ∈ fib d L N₀ k k z,
          compWeight L a₁ (G.layerIndex s) / ((L : ℝ) ^ G.layerIndex s) ^ 2 *
            ‖leafField G ψ s - leafAvg G φ s‖ ^ 2) +
        3 / 2 * βk * (varsigmaBar G ϖ z * Mψ) ^ 2 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hLk : 0 < (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hβ0def : betaCanon d L βk k 0 = βk / (L : ℝ) ^ (k * (d - 2)) := by
    unfold betaCanon; simp
  have hβ0 : 0 ≤ betaCanon d L βk k 0 := by rw [hβ0def]; positivity
  have hβk : βk = betaCanon d L βk k 0 * (L : ℝ) ^ (k * (d - 2)) := by
    rw [hβ0def]; field_simp
  have hVpos : 0 < blockVol d L k := by unfold blockVol; positivity
  have hcard : ((fib d L N₀ k k z).card : ℝ) = blockVol d L k := by
    rw [card_fib le_rfl, blockVol_eq]; push_cast; rfl
  have hn : ∀ s ∈ fib d L N₀ k k z, 1 ≤ G.layerIndex s ∧ G.layerIndex s < k := fun s hs =>
    layerIndex_range G hXΩ (hz hs)
  have haZ : (compWeightZ G a₁ z)⁻¹ = (blockVol d L k)⁻¹ *
      ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹ := by
    unfold compWeightZ; rw [inv_inv]
  have haZ2 : compWeightZ G a₁ z ≤ 2 := by
    have hge : ∀ s ∈ fib d L N₀ k k z, (1 / 2 : ℝ) ≤ (compWeight L a₁ (k - G.layerIndex s))⁻¹ := by
      intro s hs
      have := hn s hs
      have h2 := (hadm (k - G.layerIndex s) (by omega) (by omega)).2
      have h0 := (hadm (k - G.layerIndex s) (by omega) (by omega)).1
      rw [one_div]
      exact inv_anti₀ (by linarith) h2 |>.trans_eq' rfl
    have hsum : (fib d L N₀ k k z).card • (1 / 2 : ℝ) ≤
        ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹ :=
      Finset.card_nsmul_le_sum _ _ _ hge
    rw [nsmul_eq_mul, hcard] at hsum
    have hpos : 0 < (compWeightZ G a₁ z)⁻¹ := by
      rw [haZ]
      have : 0 < ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹ := by
        refine lt_of_lt_of_le ?_ hsum
        positivity
      positivity
    have : 1 / 2 ≤ (compWeightZ G a₁ z)⁻¹ := by
      rw [haZ]
      calc (1 / 2 : ℝ) = (blockVol d L k)⁻¹ * (blockVol d L k * (1 / 2)) := by
            field_simp
        _ ≤ _ := by gcongr
    rw [← inv_inv (compWeightZ G a₁ z)]
    calc ((compWeightZ G a₁ z)⁻¹)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) this
      _ = 2 := by norm_num
  have hMnn : ∀ s ∈ fib d L N₀ k k z, ‖leafField G ψ s‖ ≤ Mψ := fun s hs => hM s (hz hs)
  -- the shift of the mean
  have hsh : ‖compMean G ϖ ψ z - compMean G (fun _ => 1) ψ z‖ ≤ varsigmaBar G ϖ z * Mψ := by
    have e : compMean G ϖ ψ z - compMean G (fun _ => 1) ψ z =
        (blockVol d L k)⁻¹ • ∑ s ∈ fib d L N₀ k k z,
          (ϖ (G.layerIndex s) - 1) • leafField G ψ s := by
      unfold compMean
      rw [← smul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [sub_smul, one_smul]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hVpos)]
    unfold varsigmaBar
    rw [mul_assoc, Finset.sum_mul]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hVpos).le
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hMnn s hs) (abs_nonneg _)
  have key := block_dominates_actual hL hd ha₁ (fib d L N₀ k k z) G.layerIndex hcard rfl hn haZ
    haZ2 hη0 hη haN hβ0
    (ψ k z - compMean G (fun _ => 1) ψ z)
    (compMean G ϖ ψ z - compMean G (fun _ => 1) ψ z) hsh
    (fun s => leafField G ψ s - leafAvg G φ s)
  have e1 : ψ k z - compMean G (fun _ => 1) ψ z +
      (blockVol d L k)⁻¹ • ∑ s ∈ fib d L N₀ k k z, (leafField G ψ s - leafAvg G φ s) =
      ψ k z - bavgL d L N₀ k k φ z := by
    rw [bavg_block G hX hXΩ hz φ, Finset.sum_sub_distrib, smul_sub]
    unfold compMean
    simp only [one_smul]
    abel
  have e2 : ψ k z - compMean G (fun _ => 1) ψ z -
      (compMean G ϖ ψ z - compMean G (fun _ => 1) ψ z) = ψ k z - compMean G ϖ ψ z := by abel
  rw [e1, e2] at key
  rw [← hβk] at key
  exact key

/-- The assembly of the blockwise inequalities into the inequality between the actions. -/
theorem composed_assemble (G : GeneratingSet d L N₀ k ϱ) (hk : 1 ≤ k) (hd : 2 ≤ d) (a : ℕ → ℝ)
    {μ : ℝ} (hμ : 0 ≤ μ) (h : EuclideanSpace ℝ (Fin Nspin)) (X : Finset (Site d L N₀ k))
    (hXΩ : ∀ s ∈ X, s ∈ G.Ω 1 ∧ s ∉ G.Ω k) (hXk : IsBlockUnion L N₀ k k X)
    (hX : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (X ∩ G.layer n))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) {βk : ℝ} (hβ : 0 ≤ βk) (ϖ : ℕ → ℝ)
    (aN : Blk d L N₀ k k → ℝ) {c : ℝ} (hc1 : c ≤ 1) (err : Blk d L N₀ k k → ℝ)
    (hblock : ∀ z ∈ tBlocks d L N₀ k k X, c * (betaCanon d L βk k 0 * (1 / 2 *
        (a k * (L : ℝ) ^ (k * (d - 2)) * ‖ψ k z - bavgL d L N₀ k k φ z‖ ^ 2))) ≤
      1 / 2 * βk * aN z * ‖ψ k z - compMean G ϖ ψ z‖ ^ 2 +
        betaCanon d L βk k 0 * (1 / 2 * ∑ s ∈ fib d L N₀ k k z,
          a (G.layerIndex s) / ((L : ℝ) ^ G.layerIndex s) ^ 2 *
            ‖leafField G ψ s - leafAvg G φ s‖ ^ 2) + err z) :
    c * multiAction (singleGen d L N₀ k ϱ) a βk μ h X ψ φ - ∑ z ∈ tBlocks d L N₀ k k X, err z ≤
      composedGauss G βk aN ϖ ψ X + multiAction G a βk μ h X ψ φ := by
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact_mod_cast this
  have hLk : 0 < (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hβ0def : betaCanon d L βk k 0 = βk / (L : ℝ) ^ (k * (d - 2)) := by
    unfold betaCanon; simp
  have hβ0 : 0 ≤ betaCanon d L βk k 0 := by rw [hβ0def]; positivity
  set β0 := betaCanon d L βk k 0 with hβ0set
  set Rest := 1 / 2 * bondE X φ + μ / 2 * ∑ x ∈ X, ‖φ x - h‖ ^ 2 with hRest
  have hR : 0 ≤ Rest + 1 / 4 * starBondE X φ := by
    have h1 := bondE_nonneg X φ
    have h2 : 0 ≤ ∑ x ∈ X, ‖φ x - h‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have h3 := starBondE_nonneg X φ
    rw [hRest]; positivity
  have hS : actionG (singleGen d L N₀ k ϱ) a μ h X ψ φ =
      1 / 2 * ∑ z ∈ tBlocks d L N₀ k k X, a k * (L : ℝ) ^ (k * (d - 2)) *
        ‖ψ k z - bavgL d L N₀ k k φ z‖ ^ 2 + Rest := by
    rw [actionG_single hk, hRest]
    ring
  have hGa : actionG G a μ h X ψ φ =
      1 / 2 * ∑ z ∈ tBlocks d L N₀ k k X, ∑ s ∈ fib d L N₀ k k z,
        a (G.layerIndex s) / ((L : ℝ) ^ G.layerIndex s) ^ 2 *
          ‖leafField G ψ s - leafAvg G φ s‖ ^ 2 + Rest := by
    unfold actionG
    rw [blockPart_eq G hd a X hX (fun s hs => (hXΩ s hs).1) ψ φ,
      sum_eq_sum_fib hXk, hRest]
    ring
  have hsum := Finset.sum_le_sum hblock
  have hmulS : multiAction (singleGen d L N₀ k ϱ) a βk μ h X ψ φ =
      β0 * (1 / 2 * ∑ z ∈ tBlocks d L N₀ k k X, a k * (L : ℝ) ^ (k * (d - 2)) *
        ‖ψ k z - bavgL d L N₀ k k φ z‖ ^ 2 + (Rest + 1 / 4 * starBondE X φ)) := by
    unfold multiAction
    rw [hS]; ring
  have hmulG : multiAction G a βk μ h X ψ φ =
      β0 * (1 / 2 * ∑ z ∈ tBlocks d L N₀ k k X, ∑ s ∈ fib d L N₀ k k z,
        a (G.layerIndex s) / ((L : ℝ) ^ G.layerIndex s) ^ 2 *
          ‖leafField G ψ s - leafAvg G φ s‖ ^ 2 + (Rest + 1 / 4 * starBondE X φ)) := by
    unfold multiAction
    rw [hGa]; ring
  have hcomp : composedGauss G βk aN ϖ ψ X = ∑ z ∈ tBlocks d L N₀ k k X,
      1 / 2 * βk * aN z * ‖ψ k z - compMean G ϖ ψ z‖ ^ 2 := rfl
  rw [hmulS, hmulG, hcomp]
  have e1 : ∑ z ∈ tBlocks d L N₀ k k X, c * (β0 * (1 / 2 *
        (a k * (L : ℝ) ^ (k * (d - 2)) * ‖ψ k z - bavgL d L N₀ k k φ z‖ ^ 2))) =
      c * (β0 * (1 / 2 * ∑ z ∈ tBlocks d L N₀ k k X, a k * (L : ℝ) ^ (k * (d - 2)) *
        ‖ψ k z - bavgL d L N₀ k k φ z‖ ^ 2)) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have e2 : ∑ z ∈ tBlocks d L N₀ k k X, β0 * (1 / 2 * ∑ s ∈ fib d L N₀ k k z,
          a (G.layerIndex s) / ((L : ℝ) ^ G.layerIndex s) ^ 2 *
            ‖leafField G ψ s - leafAvg G φ s‖ ^ 2) =
      β0 * (1 / 2 * ∑ z ∈ tBlocks d L N₀ k k X, ∑ s ∈ fib d L N₀ k k z,
        a (G.layerIndex s) / ((L : ℝ) ^ G.layerIndex s) ^ 2 *
          ‖leafField G ψ s - leafAvg G φ s‖ ^ 2) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2] at hsum
  have hc1' : 0 ≤ β0 * (Rest + 1 / 4 * starBondE X φ) := mul_nonneg hβ0 hR
  have hc2 : c * (β0 * (Rest + 1 / 4 * starBondE X φ)) ≤ β0 * (Rest + 1 / 4 * starBondE X φ) := by
    nlinarith
  linarith

/-- **Lemma III.2.3** ((2.17′); P7 (2.17), actual composed weights).  For every value of the window
field `ψ^G` and of `ψ_k`, every field `φ`, and `X ⊂ Ω₁ ∖ Ω_k` a union of `k`-blocks (with `X ∩ Λ_n`
a union of `n`-blocks),
`𝒢^♮ + β_kA^*_k(X, 𝔹_k; ψ, φ) ≥ ½(1 - η) β_kA^*_k(X; ψ_k, φ) - 8 (Σ^♮)² N_X M_ψ²`,
where `A^*_k(X; ψ_k, φ)` is the single-scale action (`singleGen`), `η` bounds the relative error
of the composed weights `a^♮_z` (III.1.6), `Σ^♮ ≥ β_k^{1/2} max_z ς̄_z` (III.1.7), `N_X` bounds the
number of `k`-blocks of `X` (Lemma III.1.2 (d)) and `M_ψ ≥ max_x |ψ^G(x)|`. -/
theorem composed_dominates (G : GeneratingSet d L N₀ k ϱ) (hk : 1 ≤ k) (hL : 2 ≤ L) (hd : 2 ≤ d)
    {a₁ : ℝ} (ha₁ : 0 < a₁) (hadm : IsAdmissibleWeights k (compWeight L a₁)) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) (X : Finset (Site d L N₀ k))
    (hXΩ : ∀ s ∈ X, s ∈ G.Ω 1 ∧ s ∉ G.Ω k) (hXk : IsBlockUnion L N₀ k k X)
    (hX : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (X ∩ G.layer n))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) {βk : ℝ} (hβ : 0 ≤ βk) (ϖ : ℕ → ℝ)
    (aN : Blk d L N₀ k k → ℝ) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (haN : ∀ z ∈ tBlocks d L N₀ k k X,
      |aN z - compWeightZ G a₁ z| ≤ η * compWeightZ G a₁ z)
    {Mψ Sig Nbl : ℝ} (hM : ∀ s ∈ X, ‖leafField G ψ s‖ ≤ Mψ)
    (hSig : ∀ z ∈ tBlocks d L N₀ k k X, Real.sqrt βk * varsigmaBar G ϖ z ≤ Sig)
    (hN : ((tBlocks d L N₀ k k X).card : ℝ) ≤ Nbl) :
    1 / 2 * (1 - η) * multiAction (singleGen d L N₀ k ϱ) (compWeight L a₁) βk μ h X ψ φ -
        8 * Sig ^ 2 * Nbl * Mψ ^ 2 ≤
      composedGauss G βk aN ϖ ψ X + multiAction G (compWeight L a₁) βk μ h X ψ φ := by
  have hz : ∀ z ∈ tBlocks d L N₀ k k X, 3 / 2 * βk * (varsigmaBar G ϖ z * Mψ) ^ 2 ≤
      3 / 2 * (Sig ^ 2 * Mψ ^ 2) := by
    intro z hz
    have h1 := hSig z hz
    have h0 : 0 ≤ Real.sqrt βk * varsigmaBar G ϖ z := by
      have : 0 ≤ varsigmaBar G ϖ z := by
        unfold varsigmaBar blockVol
        positivity
      positivity
    have h2 : βk * varsigmaBar G ϖ z ^ 2 ≤ Sig ^ 2 := by
      have := pow_le_pow_left₀ h0 h1 2
      rw [mul_pow, Real.sq_sqrt hβ] at this
      exact this
    calc 3 / 2 * βk * (varsigmaBar G ϖ z * Mψ) ^ 2 =
        3 / 2 * (βk * varsigmaBar G ϖ z ^ 2) * Mψ ^ 2 := by ring
      _ ≤ 3 / 2 * Sig ^ 2 * Mψ ^ 2 := by gcongr
      _ = _ := by ring
  have herr : ∑ z ∈ tBlocks d L N₀ k k X, 3 / 2 * βk * (varsigmaBar G ϖ z * Mψ) ^ 2 ≤
      8 * Sig ^ 2 * Nbl * Mψ ^ 2 := by
    refine (Finset.sum_le_sum hz).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hS2 : 0 ≤ Sig ^ 2 * Mψ ^ 2 := by positivity
    nlinarith
  have := composed_assemble G hk hd (compWeight L a₁) hμ h X hXΩ hXk hX ψ φ hβ ϖ aN
    (c := 1 / 2 * (1 - η)) (by linarith)
    (fun z => 3 / 2 * βk * (varsigmaBar G ϖ z * Mψ) ^ 2)
    (fun z hz => block_final G hL hd ha₁ hadm hX hXΩ (fib_subset_of_mem_tBlocks hXk hz) ψ φ hβ ϖ
      hη0 hη (haN z hz) hM)
  linarith

/-- **Lemma III.2.3, ideal case** (P7 (2.17)): with the ideal composed weights `a_z` and means
(`ϖ ≡ 1`) the inequality holds with the factor `1` and without the last term. -/
theorem composed_dominates_ideal (G : GeneratingSet d L N₀ k ϱ) (hk : 1 ≤ k) (hL : 2 ≤ L)
    (hd : 2 ≤ d) {a₁ : ℝ} (ha₁ : 0 < a₁) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) (X : Finset (Site d L N₀ k))
    (hXΩ : ∀ s ∈ X, s ∈ G.Ω 1 ∧ s ∉ G.Ω k) (hXk : IsBlockUnion L N₀ k k X)
    (hX : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (X ∩ G.layer n))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin)) {βk : ℝ} (hβ : 0 ≤ βk) :
    multiAction (singleGen d L N₀ k ϱ) (compWeight L a₁) βk μ h X ψ φ ≤
      composedGauss G βk (compWeightZ G a₁) (fun _ => 1) ψ X +
        multiAction G (compWeight L a₁) βk μ h X ψ φ := by
  have := composed_assemble G hk hd (compWeight L a₁) hμ h X hXΩ hXk hX ψ φ hβ (fun _ => 1)
    (compWeightZ G a₁) (c := 1) le_rfl (fun _ => 0) ?_
  · simpa using this
  intro z hz
  have hfz := fib_subset_of_mem_tBlocks hXk hz
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact_mod_cast this
  have hβ0def : betaCanon d L βk k 0 = βk / (L : ℝ) ^ (k * (d - 2)) := by
    unfold betaCanon; simp
  have hβ0 : 0 ≤ betaCanon d L βk k 0 := by rw [hβ0def]; positivity
  have hβk : βk = betaCanon d L βk k 0 * (L : ℝ) ^ (k * (d - 2)) := by
    rw [hβ0def]; field_simp
  have hVpos : 0 < blockVol d L k := by unfold blockVol; positivity
  have hcard : ((fib d L N₀ k k z).card : ℝ) = blockVol d L k := by
    rw [card_fib le_rfl, blockVol_eq]; push_cast; rfl
  have hn : ∀ s ∈ fib d L N₀ k k z, 1 ≤ G.layerIndex s ∧ G.layerIndex s < k := fun s hs =>
    layerIndex_range G hXΩ (hfz hs)
  have haZ : (compWeightZ G a₁ z)⁻¹ = (blockVol d L k)⁻¹ *
      ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹ := by
    unfold compWeightZ; rw [inv_inv]
  have hdom := block_dominates hL hd ha₁ (fib d L N₀ k k z) G.layerIndex hcard rfl hn haZ
    (ψ k z - compMean G (fun _ => 1) ψ z) (fun s => leafField G ψ s - leafAvg G φ s)
  have e1 : ψ k z - compMean G (fun _ => 1) ψ z +
      (blockVol d L k)⁻¹ • ∑ s ∈ fib d L N₀ k k z, (leafField G ψ s - leafAvg G φ s) =
      ψ k z - bavgL d L N₀ k k φ z := by
    rw [bavg_block G hX hXΩ hfz φ, Finset.sum_sub_distrib, smul_sub]
    unfold compMean
    simp only [one_smul]
    abel
  rw [e1] at hdom
  set β0 := betaCanon d L βk k 0 with hβ0set
  have e3 : 1 / 2 * βk * compWeightZ G a₁ z * ‖ψ k z - compMean G (fun _ => 1) ψ z‖ ^ 2 =
      β0 * (1 / 2 * (compWeightZ G a₁ z * (L : ℝ) ^ (k * (d - 2)) *
        ‖ψ k z - compMean G (fun _ => 1) ψ z‖ ^ 2)) := by
    conv_lhs => rw [hβk]
    ring
  rw [e3]
  set T := ∑ s ∈ fib d L N₀ k k z, compWeight L a₁ (G.layerIndex s) /
    ((L : ℝ) ^ G.layerIndex s) ^ 2 * ‖leafField G ψ s - leafAvg G φ s‖ ^ 2 with hT
  have := mul_le_mul_of_nonneg_left hdom (by positivity : 0 ≤ β0 / 2)
  nlinarith

end Global
