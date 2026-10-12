/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionEngine
public import Balaban.Fluctuation.ExpansionLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The block energy of the chord form of the interaction (FLUCTUATION §2.3, §3.3)

By the chord identity (Lemma 2.3 (a), `expansion_chord`) the energy of the minimiser above the
background is
`ℰ(ψ') = (a_n/2) ‖ψ' - Q_n φ'‖² + ½⟨φ', (-Δ + ν + α_{k+1}) φ'⟩` (`levelEnergyC`, `hessForm`),
with `φ' = δφ` the fluctuation field.  The interaction potential is `V^{(k)} = ℰ` minus a polynomial of
degree `≤ 2` in `ψ'` (Lemma 2.3 (b)), so `V''' = ℰ'''`.  Here `ℰ` is split over the blocks
`B_{n+1}(z)` into the block energies `energyBlock`, which depend on the decoupled objects
`(α_{k+1}(s), δφ(s), ψ')` only through finitely many sites near the block (`energyBlock_local`),
are polynomials (`energyBlock_analytic`) and are bounded by `O(δ₁²)` on the realizable triples
(`energyBlock_bound`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset Matrix

section Energy

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

variable (Gp Hm) in
/-- **The energy density at a site `x`** of the chord form: the level term (on `Ω₁(H⁻)`) and the
quadratic form `½⟨δφ, (-Δ + ν + α_{k+1}) δφ⟩` (bonds to the right of `x`), for the fluctuation field
`δφ`, the multiplier `α = α_{k+1}` and the tangent `ψ'`. -/
noncomputable def energyDensity (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (α : Gp.Ω 1 → ℂ)
    (δφ : Hm.Ω 1 × Fin N → ℂ) (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (x : CTorus d L N₁ m₁ K) : ℂ :=
  (by classical exact if x ∈ Hm.Ω 1 then
    (((1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) * ∑ i,
      (ψ' x i - blockMean Hm n (fun y => svec Hm δφ y i) x) *
      (ψ' x i - blockMean Hm n (fun y => svec Hm δφ y i) x) else 0) +
  (1 / 2) * (∑ μ : Fin d, ∑ i, (svec Hm δφ (x + Pi.single μ 1) i - svec Hm δφ x i) *
      (svec Hm δφ (x + Pi.single μ 1) i - svec Hm δφ x i) +
    (ν : ℂ) * ∑ i, svec Hm δφ x i * svec Hm δφ x i +
    zeroExt (Gp.Ω 1) α x * ∑ i, svec Hm δφ x i * svec Hm δφ x i)

variable (Gp Hm) in
/-- **The block energy**: the sum of the density over the block `B_{n+1}(z)` of the fine torus. -/
noncomputable def energyBlock (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (α : Gp.Ω 1 → ℂ)
    (δφ : Hm.Ω 1 × Fin N → ℂ) (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x : CTorus d L N₁ m₁ K =>
      jBlock d L (N₁ * L ^ m₁) K (n + 1) x = z), energyDensity Gp Hm a ν n α δφ ψ' x

variable (d L N₁ m₁ K) in
/-- The sites of the block `B_{n+1}(z)`. -/
noncomputable def blockSites (n : ℕ) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter (fun x : CTorus d L N₁ m₁ K => jBlock d L (N₁ * L ^ m₁) K (n + 1) x = z)

variable (Hm) in
/-- **The sites read by the block energy**: the block, its right neighbours, and the `n`-blocks
(of `Hm`) through the block. -/
def readSites (n : ℕ) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    Set (CTorus d L N₁ m₁ K) :=
  {y | ∃ x ∈ blockSites d L N₁ m₁ K n z,
    y = x ∨ (∃ μ : Fin d, y = x + Pi.single μ 1) ∨ y ∈ Hm.blk n x}

theorem energyDensity_congr {a : ℕ → ℝ} {ν : ℝ} {n : ℕ} {α α' : Gp.Ω 1 → ℂ}
    {δφ δφ' : Hm.Ω 1 × Fin N → ℂ} {ψ ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {x : CTorus d L N₁ m₁ K}
    (hα : ∀ h : x ∈ Gp.Ω 1, α ⟨x, h⟩ = α' ⟨x, h⟩)
    (hδ : ∀ y : CTorus d L N₁ m₁ K,
      (y = x ∨ (∃ μ : Fin d, y = x + Pi.single μ 1) ∨ y ∈ Hm.blk n x) →
      ∀ i, svec Hm δφ y i = svec Hm δφ' y i)
    (hψ : ψ x = ψ' x) :
    energyDensity Gp Hm a ν n α δφ ψ x = energyDensity Gp Hm a ν n α' δφ' ψ' x := by
  classical
  have hbm : ∀ i, blockMean Hm n (fun y => svec Hm δφ y i) x =
      blockMean Hm n (fun y => svec Hm δφ' y i) x := by
    intro i
    unfold blockMean
    congr 1
    exact Finset.sum_congr rfl fun y hy => hδ y (Or.inr (Or.inr hy)) i
  have hz : zeroExt (Gp.Ω 1) α x = zeroExt (Gp.Ω 1) α' x := by
    by_cases hx : x ∈ Gp.Ω 1
    · simp only [zeroExt, hx, dite_true]; exact hα hx
    · simp [zeroExt, hx]
  unfold energyDensity
  have h0 := fun i => hδ x (Or.inl rfl) i
  have h1 := fun μ i => hδ (x + Pi.single μ 1) (Or.inr (Or.inl ⟨μ, rfl⟩)) i
  simp only [hbm, hz, h0, h1, hψ]

section Analytic

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q₀ : Q}

theorem analyticAt_svec' (δφ : Q → Hm.Ω 1 × Fin N → ℂ) (h : ∀ r, AnalyticAt ℂ (fun q => δφ q r) q₀)
    (y : CTorus d L N₁ m₁ K) (i : Fin N) : AnalyticAt ℂ (fun q => svec Hm (δφ q) y i) q₀ := by
  classical
  by_cases hy : y ∈ Hm.Ω 1
  · have : (fun q => svec Hm (δφ q) y i) = fun q => δφ q (⟨y, hy⟩, i) := by
      funext q; exact svec_of_mem Hm (δφ q) ⟨y, hy⟩ i
    rw [this]; exact h _
  · have : (fun q => svec Hm (δφ q) y i) = fun _ => 0 := by
      funext q; exact svec_of_not_mem Hm (δφ q) hy i
    rw [this]; exact analyticAt_const

theorem analyticAt_zeroExt' (α : Q → Gp.Ω 1 → ℂ) (h : ∀ r, AnalyticAt ℂ (fun q => α q r) q₀)
    (x : CTorus d L N₁ m₁ K) : AnalyticAt ℂ (fun q => zeroExt (Gp.Ω 1) (α q) x) q₀ := by
  classical
  by_cases hx : x ∈ Gp.Ω 1
  · have : (fun q => zeroExt (Gp.Ω 1) (α q) x) = fun q => α q ⟨x, hx⟩ := by
      funext q; simp [zeroExt, hx]
    rw [this]; exact h _
  · have : (fun q => zeroExt (Gp.Ω 1) (α q) x) = fun _ => 0 := by
      funext q; simp [zeroExt, hx]
    rw [this]; exact analyticAt_const

theorem analyticAt_energyDensity (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (α : Q → Gp.Ω 1 → ℂ)
    (δφ : Q → Hm.Ω 1 × Fin N → ℂ) (ψ' : Q → CTorus d L N₁ m₁ K → Fin N → ℂ)
    (hα : ∀ r, AnalyticAt ℂ (fun q => α q r) q₀) (hδ : ∀ r, AnalyticAt ℂ (fun q => δφ q r) q₀)
    (hψ : ∀ y i, AnalyticAt ℂ (fun q => ψ' q y i) q₀) (x : CTorus d L N₁ m₁ K) :
    AnalyticAt ℂ (fun q => energyDensity Gp Hm a ν n (α q) (δφ q) (ψ' q) x) q₀ := by
  classical
  have hs := analyticAt_svec' (Hm := Hm) δφ hδ
  have hz := analyticAt_zeroExt' (Gp := Gp) α hα
  have hbm : ∀ i, AnalyticAt ℂ (fun q => blockMean Hm n (fun y => svec Hm (δφ q) y i) x) q₀ := by
    intro i
    unfold blockMean
    exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun y _ => hs y i)
  unfold energyDensity
  have h1 : ∀ i, AnalyticAt ℂ (fun q => ψ' q x i) q₀ := fun i => hψ x i
  have h2 := hz x
  have h3 := fun y i => hs y i
  have h4 := hbm
  split_ifs with hx
  · fun_prop
  · fun_prop

theorem analyticAt_energyBlock (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (α : Q → Gp.Ω 1 → ℂ)
    (δφ : Q → Hm.Ω 1 × Fin N → ℂ) (ψ' : Q → CTorus d L N₁ m₁ K → Fin N → ℂ)
    (hα : ∀ r, AnalyticAt ℂ (fun q => α q r) q₀) (hδ : ∀ r, AnalyticAt ℂ (fun q => δφ q r) q₀)
    (hψ : ∀ y i, AnalyticAt ℂ (fun q => ψ' q y i) q₀)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    AnalyticAt ℂ (fun q => energyBlock Gp Hm a ν n (α q) (δφ q) (ψ' q) z) q₀ := by
  unfold energyBlock
  exact Finset.analyticAt_fun_sum _ fun x _ => analyticAt_energyDensity a ν n α δφ ψ' hα hδ hψ x

end Analytic

section Bound

theorem card_blockSites_le (Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm) (n : ℕ) (hn : n + 1 ≤ K)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    ((blockSites d L N₁ m₁ K n z).card : ℝ) ≤ ((L : ℝ) ^ (n + 1)) ^ d := by
  classical
  by_cases hz : (blockSites d L N₁ m₁ K n z).Nonempty
  · obtain ⟨y, hy⟩ := hz
    have hyz : jBlock d L (N₁ * L ^ m₁) K (n + 1) y = z := (Finset.mem_filter.1 hy).2
    have e : blockSites d L N₁ m₁ K n z = Hm.blk (n + 1) y := by
      ext x
      rw [GeneratingSet.mem_blk, ← hyz]
      simp [blockSites]
    rw [e, card_blk Hm (n + 1) hn y]
    push_cast
    exact le_rfl
  · rw [Finset.not_nonempty_iff_eq_empty.1 hz, Finset.card_empty]
    simp only [Nat.cast_zero]
    positivity

/-- **The pointwise bound of the energy density.** -/
theorem energyDensity_bound {a : ℕ → ℝ} {ν : ℝ} {n : ℕ} (hnK : n ≤ K) (ha : 0 ≤ a n) (hν : 0 ≤ ν)
    {α : Gp.Ω 1 → ℂ} {δφ : Hm.Ω 1 × Fin N → ℂ} {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {V δ ρ : ℝ} (hV : 0 ≤ V) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hsv : ∀ (y : CTorus d L N₁ m₁ K) i, ‖svec Hm δφ y i‖ ≤ V)
    (hα : ∀ x : Gp.Ω 1, Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α x‖ ≤ ρ)
    (hψ : ∀ x ∈ Hm.Ω 1, ∀ i, ‖ψ' x i‖ ≤ δ) (x : CTorus d L N₁ m₁ K) :
    ‖energyDensity Gp Hm a ν n α δφ ψ' x‖ ≤
      (1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) * (N * (δ + V) * (δ + V)) +
        (1 / 2) * (d * (N * (2 * V) * (2 * V)) + ν * (N * V * V) + ρ * (N * V * V)) := by
  classical
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLn : 0 < ((L : ℝ) ^ n) ^ 2 := by positivity
  set cn : ℝ := (1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) with hcn
  have hcn0 : 0 ≤ cn := by positivity
  unfold energyDensity
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · split_ifs with hx
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcn0]
      refine mul_le_mul_of_nonneg_left ?_ hcn0
      refine norm_sum_mul_le (P := δ + V) (Q := δ + V) (fun i => ?_) (fun i => ?_) <;>
      · refine (norm_sub_le _ _).trans (add_le_add (hψ x hx i) ?_)
        exact norm_blockMean_le' hnK _ x (fun y _ => hsv y i)
    · simp only [norm_zero]
      positivity
  · rw [norm_mul]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h12]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · refine (norm_sum_le _ _).trans ?_
      calc ∑ μ : Fin d, ‖∑ i, (svec Hm δφ (x + Pi.single μ 1) i - svec Hm δφ x i) *
            (svec Hm δφ (x + Pi.single μ 1) i - svec Hm δφ x i)‖
          ≤ ∑ _μ : Fin d, (N * (2 * V) * (2 * V)) := Finset.sum_le_sum fun μ _ =>
            norm_sum_mul_le (fun i => (norm_sub_le _ _).trans (by linarith [hsv (x + Pi.single μ 1) i, hsv x i]))
              (fun i => (norm_sub_le _ _).trans (by linarith [hsv (x + Pi.single μ 1) i, hsv x i]))
        _ = d * (N * (2 * V) * (2 * V)) := by simp
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hν]
      exact mul_le_mul_of_nonneg_left (norm_sum_mul_le (fun i => hsv x i) (fun i => hsv x i)) hν
    · rw [norm_mul]
      have hz : ‖zeroExt (Gp.Ω 1) α x‖ ≤ ρ := by
        by_cases hx : x ∈ Gp.Ω 1
        · simp only [zeroExt, hx, dite_true]
          have h1 := hα ⟨x, hx⟩
          have hsp : (1 : ℝ) ≤ Gp.spacing x ^ 2 := by
            unfold GeneratingSet.spacing
            have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := NeZero.ne L; omega : 1 ≤ L)
            exact one_le_pow₀ (one_le_pow₀ hL1)
          nlinarith [norm_nonneg (α ⟨x, hx⟩)]
        · simp [zeroExt, hx]; exact hρ
      exact mul_le_mul hz (norm_sum_mul_le (fun i => hsv x i) (fun i => hsv x i)) (norm_nonneg _) hρ

variable (d L N) in
/-- **The explicit bound of the block energy** on the realizable triples:
`(L^{n+1})^d · (c_n N (δ + V)² + ½ N V² (4d + ν + ρ))`, `c_n = ½ a_n / L^{2n}`. -/
noncomputable def energyBd (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (V δ ρ : ℝ) : ℝ :=
  ((L : ℝ) ^ (n + 1)) ^ d * ((1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) * (N * (δ + V) * (δ + V)) +
    (1 / 2) * (d * (N * (2 * V) * (2 * V)) + ν * (N * V * V) + ρ * (N * V * V)))

/-- **The bound of the block energy.** -/
theorem energyBlock_bound {a : ℕ → ℝ} {ν : ℝ} {n : ℕ} (hn : n + 1 ≤ K) (ha : 0 ≤ a n)
    (hν : 0 ≤ ν) {α : Gp.Ω 1 → ℂ} {δφ : Hm.Ω 1 × Fin N → ℂ}
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} {V δ ρ : ℝ} (hV : 0 ≤ V) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hsv : ∀ (y : CTorus d L N₁ m₁ K) i, ‖svec Hm δφ y i‖ ≤ V)
    (hα : ∀ x : Gp.Ω 1, Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α x‖ ≤ ρ)
    (hψ : ∀ x ∈ Hm.Ω 1, ∀ i, ‖ψ' x i‖ ≤ δ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    ‖energyBlock Gp Hm a ν n α δφ ψ' z‖ ≤ energyBd d L N a ν n V δ ρ := by
  classical
  have hd := fun x => energyDensity_bound (Gp := Gp) (Hm := Hm) (by omega : n ≤ K) ha hν hV hδ hρ
    hsv hα hψ x
  have hB0 : 0 ≤ (1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) * (N * (δ + V) * (δ + V)) +
      (1 / 2) * (d * (N * (2 * V) * (2 * V)) + ν * (N * V * V) + ρ * (N * V * V)) :=
    (norm_nonneg _).trans (hd 0)
  unfold energyBlock energyBd
  calc _ ≤ ∑ x ∈ Finset.univ.filter (fun x : CTorus d L N₁ m₁ K =>
          jBlock d L (N₁ * L ^ m₁) K (n + 1) x = z),
        ‖energyDensity Gp Hm a ν n α δφ ψ' x‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ Finset.univ.filter (fun x : CTorus d L N₁ m₁ K =>
          jBlock d L (N₁ * L ^ m₁) K (n + 1) x = z),
        ((1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) * (N * (δ + V) * (δ + V)) +
        (1 / 2) * (d * (N * (2 * V) * (2 * V)) + ν * (N * V * V) + ρ * (N * V * V))) :=
        Finset.sum_le_sum fun x _ => hd x
    _ = (blockSites d L N₁ m₁ K n z).card * _ := by
        rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (card_blockSites_le Hm n hn z) hB0

end Bound

end Energy

end Balaban.Localization
