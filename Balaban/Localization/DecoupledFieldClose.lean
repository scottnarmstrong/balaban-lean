/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledFieldLocal
public import Balaban.Localization.DecoupledClose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem I-4a (d): closeness of the decoupled system to `s = 1` away from the parameters

Weights, weighted local bounds of the commutator and of the quadratic remainder (by cutting a
field off outside the neighbourhood of a site, so that the unweighted local bounds of
`Balaban/Background/Calculus.lean` apply), and the a priori estimate for the difference of the
solutions at `s` and at `s = 1`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Weights

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- The path distance to the set `W`, truncated at `t`. -/
noncomputable def truncSetDist (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (W : Finset (CTorus d L N₁ m₁ K)) (t : ℝ) (x : CTorus d L N₁ m₁ K) : ENNReal :=
  min (siteSetDist G W x) (ENNReal.ofReal t)

theorem truncSetDist_ne_top (W : Finset (CTorus d L N₁ m₁ K)) (t : ℝ) (x : CTorus d L N₁ m₁ K) :
    truncSetDist G W t x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)

theorem truncSetDist_triangle (W : Finset (CTorus d L N₁ m₁ K)) (t : ℝ)
    (x y : CTorus d L N₁ m₁ K) :
    truncSetDist G W t x ≤ G.pathDist x y + truncSetDist G W t y := by
  unfold truncSetDist
  have h := setDist_triangle (G := G) W x y
  rcases le_total (siteSetDist G W y) (ENNReal.ofReal t) with h' | h'
  · rw [min_eq_left h']; exact (min_le_left _ _).trans h
  · rw [min_eq_right h']; exact (min_le_right _ _).trans le_add_self

/-- The exponential weight `e^{ε min(d(x, W), t)}`. -/
noncomputable def wgt (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (W : Finset (CTorus d L N₁ m₁ K))
    (t ε : ℝ) (x : CTorus d L N₁ m₁ K) : ℝ :=
  Real.exp (ε * (truncSetDist G W t x).toReal)

theorem isWeight_wgt (W : Finset (CTorus d L N₁ m₁ K)) (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    IsWeight G ε (wgt G W t ε) := by
  have := isWeight_of_dist G hε (T := 1) le_rfl (truncSetDist G W t)
    (truncSetDist_triangle W t)
  have e : (fun x => if truncSetDist G W t x = ⊤ then (1 : ℝ) else
      Real.exp (ε * (truncSetDist G W t x).toReal)) = wgt G W t ε := by
    funext x; simp [wgt, truncSetDist_ne_top]
  rwa [e] at this

theorem wgt_pos (W : Finset (CTorus d L N₁ m₁ K)) (t ε : ℝ) (x : CTorus d L N₁ m₁ K) :
    0 < wgt G W t ε x := Real.exp_pos _

/-- The weight changes by at most `e^{ε c}` over path distance `c`. -/
theorem weight_le_of_pathDist {ε : ℝ} (hε : 0 ≤ ε) {w : CTorus d L N₁ m₁ K → ℝ}
    (hw : IsWeight G ε w) {x y : CTorus d L N₁ m₁ K} {c : ℝ} (hc : 0 ≤ c)
    (h : G.pathDist x y ≤ ENNReal.ofReal c) : w x ≤ Real.exp (ε * c) * w y := by
  have h1 := decay_ofReal_ge hε hc h
  have h2 := hw.2 x y
  have hx : 0 < w x := lt_of_lt_of_le zero_lt_one (hw.1 x)
  have h3 : w x * Real.exp (-(ε * c)) ≤ w y :=
    (mul_le_mul_of_nonneg_left h1 hx.le).trans h2
  have e : Real.exp (ε * c) * Real.exp (-(ε * c)) = 1 := by
    rw [← Real.exp_add]; simp
  calc w x = Real.exp (ε * c) * (w x * Real.exp (-(ε * c))) := by
        rw [← mul_assoc, mul_comm (Real.exp _) (w x), mul_assoc, e, mul_one]
    _ ≤ Real.exp (ε * c) * w y := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le

/-- The sites of `Ω₁` that the row of `H_D` at `x` can see: `x`, its neighbours and its block. -/
def NearSite (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (x y : CTorus d L N₁ m₁ K) : Prop :=
  y = x ∨ (∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) ∨
    y ∈ G.blk (G.layerIndex x) x

/-- Near sites are within path distance `2 d`. -/
theorem pathDist_near_le (hd : 1 ≤ d) {x y : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1) (hy : y ∈ G.Ω 1)
    (h : NearSite G x y) : G.pathDist x y ≤ ENNReal.ofReal (2 * d) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rcases h with rfl | ⟨μ, hμ⟩ | hb
  · rw [G.pathDist_self hx]; exact bot_le
  · refine (pathDist_adj_le_one hx hy ?_).trans (ENNReal.ofReal_le_ofReal (by linarith))
    rcases hμ with rfl | rfl
    · exact ⟨μ, Or.inl rfl⟩
    · exact ⟨μ, Or.inr (by simp)⟩
  · obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
    exact G.pathDist_block_le hj1 hjk hxl (G.mem_blk.1 hb)

variable {a : ℕ → ℝ} {ν : ℝ}

theorem nearSite_of_entry_ne_zero (α : G.Ω 1 → ℂ) {x y : G.Ω 1}
    (h : dirichletOperator G a ν α x y ≠ 0) :
    NearSite G (x : CTorus d L N₁ m₁ K) (y : CTorus d L N₁ m₁ K) := by
  by_contra hn
  apply h
  apply dirichlet_entry_eq_zero (G := G) α
  · intro hyx; exact hn (Or.inl hyx)
  · intro μ; exact ⟨fun h' => hn (Or.inr (Or.inl ⟨μ, Or.inl h'⟩)),
      fun h' => hn (Or.inr (Or.inl ⟨μ, Or.inr h'⟩))⟩
  · intro hb; exact hn (Or.inr (Or.inr hb))

end Weights

section LocalComm

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L N₀ k ϱ)

/-- **The commutator bound with the gradient hypotheses at one site only** (the proof of
`commK_sup_bound` uses the gradients at the site `x` alone). -/
theorem commK_local_bound' (hd : 0 < d) (hL : 1 ≤ L) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a)
    (ν : ℝ) (α : G.Ω 1 → ℂ) {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ) (s : G.Ω 1 × Fin N → ℂ) {V : ℝ} (hV0 : 0 ≤ V)
    (hV : ∀ y i, ‖svec G s y i‖ ≤ V)
    (x : G.Ω 1)
    (hf : ∀ (μ : Fin d) (i : Fin N),
      G.spacing x * ‖svec G s ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i - svec G s x i‖ ≤ V)
    (hb : ∀ (μ : Fin d) (i : Fin N),
      G.spacing x * ‖svec G s ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i - svec G s x i‖ ≤ L * V) :
    G.spacing x ^ 2 * ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖ ≤
      commKConst d L N * δ * V := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec x.2
  set j := G.layerIndex (x : Torus d (N₀ * L ^ k)) with hjdef
  have hsp : G.spacing x = (L : ℝ) ^ j := G.spacing_eq hj1 hjk hxl
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have h := commK_pointwise G ha ν α hφ hδ (isAgmonWeight_zero G) (le_refl (0 : ℝ)) s hj1 hjk x hxl
  simp only [zero_mul, Real.exp_zero, one_mul, mul_one] at h
  rw [hsp] at h ⊢
  set p : Torus d (N₀ * L ^ k) := (x : Torus d (N₀ * L ^ k)) with hp
  set ℓ : ℝ := (L : ℝ) ^ j with hℓ
  have hNV : 0 ≤ (N : ℝ) * V := by positivity
  -- vector norms
  have hvx : vn (svec G s p) ≤ N * V := vn_le_card_mul hV0 (hV _)
  have hvf : ∀ μ : Fin d, ℓ * vn (svec G s (p + Pi.single μ 1) - svec G s p) ≤ N * V := by
    intro μ
    have hm : 0 ≤ V / ℓ := by positivity
    have := vn_le_card_mul (v := svec G s (p + Pi.single μ 1) - svec G s p) hm (fun i => by
      rw [le_div_iff₀ hLj, mul_comm]
      have := hf μ i
      rw [hsp] at this
      simpa using this)
    calc ℓ * vn _ ≤ ℓ * (N * (V / ℓ)) := mul_le_mul_of_nonneg_left this hLj.le
      _ = N * V := by field_simp
  have hvb : ∀ μ : Fin d, ℓ * vn (svec G s (p - Pi.single μ 1) - svec G s p) ≤ N * (L * V) := by
    intro μ
    have hm : 0 ≤ L * V / ℓ := by positivity
    have := vn_le_card_mul (v := svec G s (p - Pi.single μ 1) - svec G s p) hm (fun i => by
      rw [le_div_iff₀ hLj, mul_comm]
      have := hb μ i
      rw [hsp] at this
      simpa using this)
    calc ℓ * vn _ ≤ ℓ * (N * (L * V / ℓ)) := mul_le_mul_of_nonneg_left this hLj.le
      _ = N * (L * V) := by field_simp
  -- the block average
  have hblk : (((L : ℝ) ^ j) ^ d)⁻¹ * ∑ y ∈ G.blk j p, vn (svec G s y) ≤ N * V := by
    have hc := card_blk_cast G j hjk x
    have hsum : ∑ y ∈ G.blk j p, vn (svec G s y) ≤ (G.blk j p).card * (N * V) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun y _ => vn_le_card_mul hV0 (hV _)
    rw [hc] at hsum
    have hp : (0 : ℝ) < ((L : ℝ) ^ j) ^ d := by positivity
    rw [inv_mul_le_iff₀ hp]
    linarith
  have hsumμ : (∑ μ : Fin d, (vn (svec G s (p + Pi.single μ 1) - svec G s p) +
      vn (svec G s (p - Pi.single μ 1) - svec G s p))) * ℓ ≤ d * (N * V + N * (L * V)) := by
    rw [Finset.sum_mul]
    calc _ ≤ ∑ _μ : Fin d, (N * V + N * (L * V)) := by
          refine Finset.sum_le_sum fun μ _ => ?_
          have := hvf μ
          have := hvb μ
          nlinarith
      _ = _ := by simp; ring
  -- assemble
  have hlead : ℓ * ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖ ≤ _ := h
  have hb2 : 0 ≤ ∑ μ : Fin d, (vn (svec G s (p + Pi.single μ 1) - svec G s p) +
      vn (svec G s (p - Pi.single μ 1) - svec G s p)) :=
    Finset.sum_nonneg fun μ _ => add_nonneg (vn_nonneg _) (vn_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hlead hLj.le
  calc ℓ ^ 2 * ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖
      = ℓ * (ℓ * ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖) := by ring
    _ ≤ _ := hmul
    _ ≤ commKConst d L N * δ * V := by
        unfold commKConst
        have e : ∀ A B C : ℝ, ℓ * (δ * A + δ * ℓ⁻¹ * B + 4 * d * δ * ℓ⁻¹ * C) =
            δ * (A * ℓ) + δ * B + 4 * d * δ * C := by
          intro A B C; field_simp
        rw [e]
        have h1 := mul_le_mul_of_nonneg_left hsumμ hδ
        have h2 := mul_le_mul_of_nonneg_left hvx hδ
        have h3 := mul_le_mul_of_nonneg_left hblk (by positivity : (0 : ℝ) ≤ 4 * d * δ)
        have h4 : 0 ≤ (d : ℝ) * (L - 1) * N * V * δ := by
          have : (0 : ℝ) ≤ L - 1 := by linarith
          positivity
        nlinarith

end LocalComm

section Cutoff

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

open Classical in
/-- The vector field cut off outside the near sites of `x`. -/
noncomputable def cutoffV (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (x : CTorus d L N₁ m₁ K)
    (s : G.Ω 1 × Fin N → ℂ) : G.Ω 1 × Fin N → ℂ :=
  fun p => if NearSite G x (p.1 : CTorus d L N₁ m₁ K) then s p else 0

theorem svec_cutoffV (x : CTorus d L N₁ m₁ K) (s : G.Ω 1 × Fin N → ℂ) (y : CTorus d L N₁ m₁ K)
    (i : Fin N) :
    svec G (cutoffV G x s) y i = by
      classical exact if NearSite G x y then svec G s y i else 0 := by
  classical
  unfold svec zeroExt cutoffV
  by_cases hy : y ∈ G.Ω 1
  · simp only [hy, ↓reduceDIte]
  · simp [hy]

theorem commK_cutoff (α : G.Ω 1 → ℂ) {φ : CTorus d L N₁ m₁ K → Fin N → ℂ} (s : G.Ω 1 × Fin N → ℂ)
    (x : G.Ω 1) :
    (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ cutoffV G x s) x =
      (commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x := by
  classical
  rw [commK_mulVec, commK_mulVec]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases h0 : dirichletOperator G a ν α x y = 0
  · simp [h0]
  · have hn := nearSite_of_entry_ne_zero (a := a) (ν := ν) α h0
    simp only [cutoffV, hn, ↓reduceIte]

/-- **The weighted commutator bound.**  If `ω` is a weight of rate `ε`, `ω |s̃| ≤ E` at all sites and
the weighted gradients at `x` are at most `E` (resp. `L E`), then
`ω(x) ℓ(x)² |K s (x)| ≤ c δ e^{2 d ε} E`. -/
theorem commK_weighted (S : GreenSetting G a ν) (α : G.Ω 1 → ℂ) {δ : ℝ}
    {φ : CTorus d L N₁ m₁ K → Fin N → ℂ} (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ)
    {ε : ℝ} (hε : 0 ≤ ε) {ω : CTorus d L N₁ m₁ K → ℝ} (hω : IsWeight G ε ω)
    (s : G.Ω 1 × Fin N → ℂ) {E : ℝ} (hE : 0 ≤ E)
    (hV : ∀ y i, ω y * ‖svec G s y i‖ ≤ E) (x : G.Ω 1)
    (hf : ∀ (μ : Fin d) (i : Fin N), ω x * (G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖svec G s ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i - svec G s x i‖) ≤ E)
    (hb : ∀ (μ : Fin d) (i : Fin N), ω x * (G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖svec G s ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i - svec G s x i‖) ≤ L * E) :
    ω x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖) ≤
      commKConst d L N * δ * (Real.exp (ε * (2 * d)) * E) := by
  classical
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hωx : 0 < ω x := lt_of_lt_of_le zero_lt_one (hω.1 x)
  have hEe : 1 ≤ Real.exp (ε * (2 * d)) := Real.one_le_exp (by positivity)
  set V : ℝ := Real.exp (ε * (2 * d)) * E / ω x with hVdef
  have hV0 : 0 ≤ V := by positivity
  have hVE : E / ω x ≤ V := by
    rw [hVdef]; exact div_le_div_of_nonneg_right (by nlinarith) hωx.le
  have hs : ∀ y i, ‖svec G (cutoffV G x s) y i‖ ≤ V := by
    intro y i
    rw [svec_cutoffV]
    split_ifs with hn
    · by_cases hyΩ : y ∈ G.Ω 1
      · have hpd := pathDist_near_le hd1 x.2 hyΩ hn
        have h1 := weight_le_of_pathDist hε hω (by positivity : (0 : ℝ) ≤ 2 * d) hpd
        have h2 := hV y i
        rw [hVdef, le_div_iff₀ hωx]
        calc ‖svec G s y i‖ * ω x ≤ ‖svec G s y i‖ * (Real.exp (ε * (2 * d)) * ω y) :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = Real.exp (ε * (2 * d)) * (ω y * ‖svec G s y i‖) := by ring
          _ ≤ Real.exp (ε * (2 * d)) * E := mul_le_mul_of_nonneg_left h2 (by positivity)
      · have : svec G s y i = 0 := svec_of_not_mem G s hyΩ i
        rw [this, norm_zero]; exact hV0
    · rw [norm_zero]; exact hV0
  have hnear_nb : ∀ μ : Fin d, NearSite G (x : CTorus d L N₁ m₁ K)
      ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) ∧ NearSite G (x : CTorus d L N₁ m₁ K)
      ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) := fun μ =>
    ⟨Or.inr (Or.inl ⟨μ, Or.inl rfl⟩), Or.inr (Or.inl ⟨μ, Or.inr rfl⟩)⟩
  have hnear_x : NearSite G (x : CTorus d L N₁ m₁ K) (x : CTorus d L N₁ m₁ K) := Or.inl rfl
  have hsp : 0 < G.spacing (x : CTorus d L N₁ m₁ K) := spacing_pos G
  have hfs : ∀ (μ : Fin d) (i : Fin N), G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖svec G (cutoffV G x s) ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i -
        svec G (cutoffV G x s) x i‖ ≤ V := by
    intro μ i
    rw [svec_cutoffV, svec_cutoffV]
    simp only [(hnear_nb μ).1, hnear_x, ↓reduceIte]
    have := hf μ i
    rw [← mul_assoc, mul_comm (ω x), mul_assoc] at this
    have h2 : G.spacing (x : CTorus d L N₁ m₁ K) *
        ‖svec G s ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i - svec G s x i‖ ≤ E / ω x := by
      rw [le_div_iff₀ hωx, mul_comm]; exact this.trans' (le_of_eq (by ring))
    exact h2.trans hVE
  have hbs : ∀ (μ : Fin d) (i : Fin N), G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖svec G (cutoffV G x s) ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i -
        svec G (cutoffV G x s) x i‖ ≤ L * V := by
    intro μ i
    rw [svec_cutoffV, svec_cutoffV]
    simp only [(hnear_nb μ).2, hnear_x, ↓reduceIte]
    have := hb μ i
    have h2 : G.spacing (x : CTorus d L N₁ m₁ K) *
        ‖svec G s ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i - svec G s x i‖ ≤ L * E / ω x := by
      rw [le_div_iff₀ hωx, mul_comm]; exact this.trans' (le_of_eq (by ring))
    calc _ ≤ L * E / ω x := h2
      _ = L * (E / ω x) := by ring
      _ ≤ L * V := mul_le_mul_of_nonneg_left hVE (by positivity)
  have hmain := commK_local_bound' G (by omega) (by have := S.hL; omega) S.weights ν α hφ hδ
    (cutoffV G x s) hV0 hs x hfs hbs
  rw [commK_cutoff] at hmain
  calc ω x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖_‖)
      ≤ ω x * (commKConst d L N * δ * V) := mul_le_mul_of_nonneg_left hmain hωx.le
    _ = commKConst d L N * δ * (Real.exp (ε * (2 * d)) * E) := by
        rw [hVdef]; field_simp


open Classical in
/-- The scalar field cut off outside the near sites of `x`. -/
noncomputable def cutoffS (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (x : CTorus d L N₁ m₁ K)
    (u : G.Ω 1 → ℂ) : G.Ω 1 → ℂ :=
  fun y => if NearSite G x (y : CTorus d L N₁ m₁ K) then u y else 0

theorem zeroExt_cutoffS (x : CTorus d L N₁ m₁ K) (u : G.Ω 1 → ℂ) (y : CTorus d L N₁ m₁ K) :
    zeroExt (G.Ω 1) (cutoffS G x u) y = by
      classical exact if NearSite G x y then zeroExt (G.Ω 1) u y else 0 := by
  classical
  unfold zeroExt cutoffS
  by_cases hy : y ∈ G.Ω 1
  · simp only [hy, ↓reduceDIte]
  · simp [hy]

theorem Rsc_cutoff (α : G.Ω 1 → ℂ) (u w : G.Ω 1 → ℂ) (x : G.Ω 1) :
    Rsc (dirichletOperator G a ν α) (cutoffS G x u) w x =
      Rsc (dirichletOperator G a ν α) u w x := by
  classical
  unfold Rsc
  simp only [Pi.sub_apply, Pi.mul_apply, Matrix.mulVec, dotProduct]
  have e : ∀ y : G.Ω 1, dirichletOperator G a ν α x y * cutoffS G x u y =
      dirichletOperator G a ν α x y * u y := by
    intro y
    by_cases h0 : dirichletOperator G a ν α x y = 0
    · simp [h0]
    · have hn := nearSite_of_entry_ne_zero (a := a) (ν := ν) α h0
      simp only [cutoffS, hn, ↓reduceIte]
  have e1 : ∑ y, dirichletOperator G a ν α x y * (cutoffS G x u y * w y) =
      ∑ y, dirichletOperator G a ν α x y * (u y * w y) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h0 : dirichletOperator G a ν α x y = 0
    · simp [h0]
    · have hn := nearSite_of_entry_ne_zero (a := a) (ν := ν) α h0
      simp only [cutoffS, hn, ↓reduceIte]
  have e2 : ∑ y, dirichletOperator G a ν α x y * cutoffS G x u y =
      ∑ y, dirichletOperator G a ν α x y * u y := Finset.sum_congr rfl fun y _ => e y
  have hx : cutoffS G x u x = u x := by simp [cutoffS, NearSite]
  rw [e1, e2, hx]

/-- **The weighted bound for the scalar remainder** (one factor weighted, one plain). -/
theorem Rsc_weighted (S : GreenSetting G a ν) {α : G.Ω 1 → ℂ} {x : G.Ω 1}
    (hα : G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α x‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) {ω : CTorus d L N₁ m₁ K → ℝ} (hω : IsWeight G ε ω)
    {u w : G.Ω 1 → ℂ} {E W : ℝ} (hE : 0 ≤ E) (hW : 0 ≤ W)
    (hu0 : ∀ y, ω y * ‖zeroExt (G.Ω 1) u y‖ ≤ E) (hw0 : ∀ y, ‖zeroExt (G.Ω 1) w y‖ ≤ W)
    (hu1 : ∀ μ : Fin d, ω x * (G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖zeroExt (G.Ω 1) u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - u x‖) ≤ E)
    (hu2 : ∀ μ : Fin d, ω x * (G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖zeroExt (G.Ω 1) u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) - u x‖) ≤ E)
    (hw1 : ∀ μ : Fin d, G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖zeroExt (G.Ω 1) w ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - w x‖ ≤ W)
    (hw2 : ∀ μ : Fin d, G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖zeroExt (G.Ω 1) w ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) - w x‖ ≤ W) :
    ω x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      ‖Rsc (dirichletOperator G a ν α) u w x‖) ≤
      (2 * d + 8) * (Real.exp (ε * (2 * d)) * E * W) := by
  classical
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hωx : 0 < ω x := lt_of_lt_of_le zero_lt_one (hω.1 x)
  have hEe : 1 ≤ Real.exp (ε * (2 * d)) := Real.one_le_exp (by positivity)
  set U : ℝ := Real.exp (ε * (2 * d)) * E / ω x with hUdef
  have hU0 : 0 ≤ U := by positivity
  have hnx : NearSite G (x : CTorus d L N₁ m₁ K) (x : CTorus d L N₁ m₁ K) := Or.inl rfl
  have hnb : ∀ μ : Fin d, NearSite G (x : CTorus d L N₁ m₁ K)
      ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) ∧ NearSite G (x : CTorus d L N₁ m₁ K)
      ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) := fun μ =>
    ⟨Or.inr (Or.inl ⟨μ, Or.inl rfl⟩), Or.inr (Or.inl ⟨μ, Or.inr rfl⟩)⟩
  have hEU : E / ω x ≤ U := by
    rw [hUdef]; exact div_le_div_of_nonneg_right (by nlinarith) hωx.le
  have hνx : ν * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ S.mass) S.massLe
    exact pow_le_pow_left₀ (spacing_pos G).le (spacing_le G x.2) 2
  have hsp : 0 < G.spacing (x : CTorus d L N₁ m₁ K) := spacing_pos G
  have key := Rsc_bound S.weights S.mass hνx hα (u := cutoffS G x u) (w := w) hU0 hW
    (fun y => by
      rw [zeroExt_cutoffS]
      split_ifs with hn
      · by_cases hyΩ : y ∈ G.Ω 1
        · have hpd := pathDist_near_le hd1 x.2 hyΩ hn
          have h1 := weight_le_of_pathDist hε hω (by positivity : (0 : ℝ) ≤ 2 * d) hpd
          have h2 := hu0 y
          rw [hUdef, le_div_iff₀ hωx]
          calc ‖zeroExt (G.Ω 1) u y‖ * ω x ≤ ‖zeroExt (G.Ω 1) u y‖ *
                (Real.exp (ε * (2 * d)) * ω y) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
            _ = Real.exp (ε * (2 * d)) * (ω y * ‖zeroExt (G.Ω 1) u y‖) := by ring
            _ ≤ Real.exp (ε * (2 * d)) * E := mul_le_mul_of_nonneg_left h2 (by positivity)
        · rw [zeroExt_not_mem _ _ hyΩ, norm_zero]; exact hU0
      · rw [norm_zero]; exact hU0)
    hw0
    (fun μ => by
      rw [zeroExt_cutoffS]
      simp only [(hnb μ).1, cutoffS, hnx, ↓reduceIte]
      have h := hu1 μ
      have h2 : G.spacing (x : CTorus d L N₁ m₁ K) *
          ‖zeroExt (G.Ω 1) u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - u x‖ ≤ E / ω x := by
        rw [le_div_iff₀ hωx, mul_comm]; exact h.trans' (le_of_eq (by ring))
      exact h2.trans hEU)
    (fun μ => by
      rw [zeroExt_cutoffS]
      simp only [(hnb μ).2, cutoffS, hnx, ↓reduceIte]
      have h := hu2 μ
      have h2 : G.spacing (x : CTorus d L N₁ m₁ K) *
          ‖zeroExt (G.Ω 1) u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) - u x‖ ≤ E / ω x := by
        rw [le_div_iff₀ hωx, mul_comm]; exact h.trans' (le_of_eq (by ring))
      exact h2.trans hEU)
    hw1 hw2
  rw [Rsc_cutoff] at key
  calc ω x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖Rsc (dirichletOperator G a ν α) u w x‖)
      ≤ ω x * ((2 * d + 8) * (U * W)) := mul_le_mul_of_nonneg_left key hωx.le
    _ = (2 * d + 8) * (Real.exp (ε * (2 * d)) * E * W) := by rw [hUdef]; field_simp


/-- **The weighted bound for the vector remainder** (`v` weighted, `u` plain). -/
theorem Rvec_weighted (S : GreenSetting G a ν) {α : G.Ω 1 → ℂ} {x : G.Ω 1}
    (hα : G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α x‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) {ω : CTorus d L N₁ m₁ K → ℝ} (hω : IsWeight G ε ω)
    {v u : G.Ω 1 × Fin N → ℂ} {E W : ℝ} (hE : 0 ≤ E) (hW : 0 ≤ W)
    (hv0 : ∀ y i, ω y * ‖svec G v y i‖ ≤ E)
    (hv1 : ∀ (μ : Fin d) (i : Fin N), ω x * (G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖svec G v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i - svec G v x i‖) ≤ E)
    (hv2 : ∀ (μ : Fin d) (i : Fin N), ω x * (G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖svec G v ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i - svec G v x i‖) ≤ E)
    (hu : StarBound G u W) :
    ω x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      ‖Rvec (dirichletOperator G a ν α) v u x‖) ≤
      N * ((2 * d + 8) * (Real.exp (ε * (2 * d)) * E * W)) := by
  have hωx : 0 < ω x := lt_of_lt_of_le zero_lt_one (hω.1 x)
  have hterm : ∀ i : Fin N, ω x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      ‖Rsc (dirichletOperator G a ν α) (comp G v i) (comp G u i) x‖) ≤
      (2 * d + 8) * (Real.exp (ε * (2 * d)) * E * W) := by
    intro i
    refine Rsc_weighted S hα hε hω hE hW (fun y => hv0 y i) (fun y => hu.val y i)
      (fun μ => ?_) (fun μ => ?_) (fun μ => ?_) (fun μ => ?_)
    · have := hv1 μ i; rwa [svec_of_mem] at this
    · have := hv2 μ i; rwa [svec_of_mem] at this
    · have := hu.fwd x x.2 μ i; rwa [svec_of_mem] at this
    · have := hu.bwd x x.2 μ i; rwa [svec_of_mem] at this
  unfold Rvec
  calc ω x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
        ‖∑ i, Rsc (dirichletOperator G a ν α) (comp G v i) (comp G u i) x‖)
      ≤ ω x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
        ∑ i, ‖Rsc (dirichletOperator G a ν α) (comp G v i) (comp G u i) x‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity))
          hωx.le
    _ = ∑ i, ω x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
        ‖Rsc (dirichletOperator G a ν α) (comp G v i) (comp G u i) x‖) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ ∑ _i : Fin N, (2 * d + 8) * (Real.exp (ε * (2 * d)) * E * W) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by simp

/-- **The weighted bound for the difference of two values of `𝒩`.** -/
theorem Nmap_diff_weighted (S : GreenSetting G a ν) {α₀ : G.Ω 1 → ℂ} {ιU : Bool} {δ₀ : ℝ}
    {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ} {Fs : G.Ω 1 × Fin N → ℂ} {Fb : ℝ}
    (hφ : IsSmoothField G δ₀ φ₀) (hδ₀ : 0 ≤ δ₀) (hFs : SrcBound G Fs Fb)
    {x : G.Ω 1} (hα : G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α₀ x‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) {ω : CTorus d L N₁ m₁ K → ℝ} (hω : IsWeight G ε ω)
    {δφ δφ' : G.Ω 1 × Fin N → ℂ} {E D D' : ℝ} (hE : 0 ≤ E) (hD : 0 ≤ D) (hD' : 0 ≤ D')
    (h1 : StarBound G δφ D) (h2 : StarBound G δφ' D')
    (hv0 : ∀ y i, ω y * ‖svec G (δφ - δφ') y i‖ ≤ E)
    (hv1 : ∀ (μ : Fin d) (i : Fin N), ω x * (G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖svec G (δφ - δφ') ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) i -
        svec G (δφ - δφ') x i‖) ≤ E)
    (hv2 : ∀ (μ : Fin d) (i : Fin N), ω x * (G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖svec G (δφ - δφ') ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) i -
        svec G (δφ - δφ') x i‖) ≤ E) :
    ω x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      ‖Nmap G (dirichletOperator G a ν α₀) ιU φ₀ Fs δφ x -
        Nmap G (dirichletOperator G a ν α₀) ιU φ₀ Fs δφ' x‖) ≤
      N * (E * Fb) + commKConst d L N * δ₀ * (Real.exp (ε * (2 * d)) * E) +
        1 / 2 * (N * ((2 * d + 8) * (Real.exp (ε * (2 * d)) * E * (D + D')))) := by
  have hωx : 0 < ω x := lt_of_lt_of_le zero_lt_one (hω.1 x)
  have hp : 0 ≤ G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 := by positivity
  set ℓ2 := G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 with hℓ2
  have t1 : ω x * (ℓ2 * ‖∑ i, (δφ - δφ') (x, i) * Fs (x, i)‖) ≤ N * (E * Fb) := by
    calc ω x * (ℓ2 * ‖∑ i, (δφ - δφ') (x, i) * Fs (x, i)‖)
        ≤ ω x * (ℓ2 * ∑ i, ‖(δφ - δφ') (x, i) * Fs (x, i)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hp) hωx.le
      _ = ∑ i, ((ω x * ‖(δφ - δφ') (x, i)‖) * (ℓ2 * ‖Fs (x, i)‖)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [norm_mul]; ring
      _ ≤ ∑ _i : Fin N, (E * Fb) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h3 : ω x * ‖(δφ - δφ') (x, i)‖ ≤ E := by
            have := hv0 x i; rwa [svec_of_mem] at this
          exact mul_le_mul h3 (hFs x i) (by positivity) hE
      _ = _ := by simp
  have t2 := commK_weighted S α₀ hφ hδ₀ hε hω (δφ - δφ') hE hv0 x hv1 (fun μ i => (hv2 μ i).trans
    (le_mul_of_one_le_left hE (by exact_mod_cast (by have := S.hL; omega : 1 ≤ L))))
  have t3 := Rvec_weighted S hα hε hω hE (add_nonneg hD hD') hv0 hv1 hv2 (h1.add h2)
  rw [Nmap_sub]
  calc ω x * (ℓ2 * ‖∑ i, (δφ - δφ') (x, i) * Fs (x, i) -
        (commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ (δφ - δφ')) x +
        1 / 2 * Rvec (dirichletOperator G a ν α₀) (δφ - δφ') (δφ + δφ') x‖)
      ≤ ω x * (ℓ2 * (‖∑ i, (δφ - δφ') (x, i) * Fs (x, i)‖ +
        ‖(commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ (δφ - δφ')) x‖ +
        ‖1 / 2 * Rvec (dirichletOperator G a ν α₀) (δφ - δφ') (δφ + δφ') x‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) hp) hωx.le
    _ = ω x * (ℓ2 * ‖∑ i, (δφ - δφ') (x, i) * Fs (x, i)‖) +
        ω x * (ℓ2 * ‖(commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ (δφ - δφ')) x‖) +
        1 / 2 * (ω x * (ℓ2 * ‖Rvec (dirichletOperator G a ν α₀) (δφ - δφ') (δφ + δφ') x‖)) := by
        simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat]
        ring
    _ ≤ _ := by linarith

end Cutoff

section WSup

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The four weighted pointwise bounds of a vector field on `Ω₁`: value, forward and backward
gradient, Laplacian (all with the weight at the site `x` and the spacing at `x`). -/
structure WSup (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (ω : CTorus d L N₁ m₁ K → ℝ)
    (u : G.Ω 1 × Fin N → ℂ) (V : ℝ) : Prop where
  val : ∀ (y : CTorus d L N₁ m₁ K) (i : Fin N), ω y * ‖svec G u y i‖ ≤ V
  fwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N), ω x * (G.spacing x *
    ‖svec G u (x + Pi.single μ 1) i - svec G u x i‖) ≤ V
  bwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N), ω x * (G.spacing x *
    ‖svec G u (x - Pi.single μ 1) i - svec G u x i‖) ≤ V
  lap : ∀ x ∈ G.Ω 1, ∀ i : Fin N, ω x * (G.spacing x ^ 2 * ‖∑ μ : Fin d, (2 * svec G u x i -
    svec G u (x + Pi.single μ 1) i - svec G u (x - Pi.single μ 1) i)‖) ≤ V

theorem WSup.mono {ω : CTorus d L N₁ m₁ K → ℝ} {u : G.Ω 1 × Fin N → ℂ} {V V' : ℝ}
    (h : WSup G ω u V) (hV : V ≤ V') : WSup G ω u V' :=
  ⟨fun y i => (h.val y i).trans hV, fun x hx μ i => (h.fwd x hx μ i).trans hV,
    fun x hx μ i => (h.bwd x hx μ i).trans hV, fun x hx i => (h.lap x hx i).trans hV⟩

theorem svec_sub' (u w : G.Ω 1 × Fin N → ℂ) (y : CTorus d L N₁ m₁ K) (i : Fin N) :
    svec G (u - w) y i = svec G u y i - svec G w y i := by
  unfold svec zeroExt
  split_ifs <;> simp

theorem WSup.add {ω : CTorus d L N₁ m₁ K → ℝ} (hω : ∀ y, 0 ≤ ω y) {u w : G.Ω 1 × Fin N → ℂ}
    {V W : ℝ} (hu : WSup G ω u V) (hw : WSup G ω w W) : WSup G ω (u + w) (V + W) := by
  refine ⟨fun y i => ?_, fun x hx μ i => ?_, fun x hx μ i => ?_, fun x hx i => ?_⟩
  · simp only [svec_add]
    calc ω y * ‖svec G u y i + svec G w y i‖ ≤ ω y * (‖svec G u y i‖ + ‖svec G w y i‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (hω y)
      _ = ω y * ‖svec G u y i‖ + ω y * ‖svec G w y i‖ := by ring
      _ ≤ V + W := add_le_add (hu.val y i) (hw.val y i)
  · simp only [svec_add]
    have hs := (spacing_pos G (x := x)).le
    calc ω x * (G.spacing x * ‖svec G u (x + Pi.single μ 1) i + svec G w (x + Pi.single μ 1) i -
          (svec G u x i + svec G w x i)‖)
        ≤ ω x * (G.spacing x * (‖svec G u (x + Pi.single μ 1) i - svec G u x i‖ +
          ‖svec G w (x + Pi.single μ 1) i - svec G w x i‖)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hs) (hω x)
          refine le_trans (le_of_eq ?_) (norm_add_le _ _)
          congr 1; ring
      _ = ω x * (G.spacing x * ‖svec G u (x + Pi.single μ 1) i - svec G u x i‖) +
          ω x * (G.spacing x * ‖svec G w (x + Pi.single μ 1) i - svec G w x i‖) := by ring
      _ ≤ V + W := add_le_add (hu.fwd x hx μ i) (hw.fwd x hx μ i)
  · simp only [svec_add]
    have hs := (spacing_pos G (x := x)).le
    calc ω x * (G.spacing x * ‖svec G u (x - Pi.single μ 1) i + svec G w (x - Pi.single μ 1) i -
          (svec G u x i + svec G w x i)‖)
        ≤ ω x * (G.spacing x * (‖svec G u (x - Pi.single μ 1) i - svec G u x i‖ +
          ‖svec G w (x - Pi.single μ 1) i - svec G w x i‖)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hs) (hω x)
          refine le_trans (le_of_eq ?_) (norm_add_le _ _)
          congr 1; ring
      _ = ω x * (G.spacing x * ‖svec G u (x - Pi.single μ 1) i - svec G u x i‖) +
          ω x * (G.spacing x * ‖svec G w (x - Pi.single μ 1) i - svec G w x i‖) := by ring
      _ ≤ V + W := add_le_add (hu.bwd x hx μ i) (hw.bwd x hx μ i)
  · simp only [svec_add]
    have hs := (sq_nonneg (G.spacing x))
    have e : ∑ μ : Fin d, (2 * (svec G u x i + svec G w x i) -
        (svec G u (x + Pi.single μ 1) i + svec G w (x + Pi.single μ 1) i) -
        (svec G u (x - Pi.single μ 1) i + svec G w (x - Pi.single μ 1) i)) =
        ∑ μ : Fin d, (2 * svec G u x i - svec G u (x + Pi.single μ 1) i -
          svec G u (x - Pi.single μ 1) i) +
        ∑ μ : Fin d, (2 * svec G w x i - svec G w (x + Pi.single μ 1) i -
          svec G w (x - Pi.single μ 1) i) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun μ _ => by ring
    rw [e]
    calc ω x * (G.spacing x ^ 2 * ‖_ + _‖)
        ≤ ω x * (G.spacing x ^ 2 * (‖∑ μ : Fin d, (2 * svec G u x i - svec G u (x + Pi.single μ 1) i -
          svec G u (x - Pi.single μ 1) i)‖ + ‖∑ μ : Fin d, (2 * svec G w x i -
          svec G w (x + Pi.single μ 1) i - svec G w (x - Pi.single μ 1) i)‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_add_le _ _) hs) (hω x)
      _ = _ := by ring
      _ ≤ V + W := add_le_add (hu.lap x hx i) (hw.lap x hx i)


/-- **From weighted scalar sources to weighted vector fields** (wall bonds cost a factor `L`, bonds
into a site a factor `e^ε`). -/
theorem wsup_liftOp (hϱ : 1 < ϱ) (hL : 2 ≤ L) {ε : ℝ} (hε : 0 ≤ ε)
    {ω : CTorus d L N₁ m₁ K → ℝ} (hω : IsWeight G ε ω)
    {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, ω x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      SupBdW G ω (zeroExt (G.Ω 1) (M *ᵥ f)) (b * C))
    (g : G.Ω 1 × Fin N → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ (x : G.Ω 1) (i : Fin N), ω x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
      ‖g (x, i)‖ ≤ C) :
    WSup G ω (liftOp N M *ᵥ g) (L * Real.exp ε * (b * C)) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hE1 : 1 ≤ Real.exp ε := Real.one_le_exp hε
  have hbC : 0 ≤ b * C := mul_nonneg hb hC
  have hLE : 1 ≤ (L : ℝ) * Real.exp ε := one_le_mul_of_one_le_of_one_le hL1 hE1
  have hmono : b * C ≤ L * Real.exp ε * (b * C) := le_mul_of_one_le_left hbC hLE
  have hsd : ∀ i : Fin N, SupBdW G ω (zeroExt (G.Ω 1) (M *ᵥ comp G g i)) (b * C) :=
    fun i => h (comp G g i) hC (fun x => hg x i)
  have hω0 : ∀ y, 0 < ω y := fun y => lt_of_lt_of_le zero_lt_one (hω.1 y)
  refine ⟨fun y i => ?_, fun x hx μ i => ?_, fun x hx μ i => ?_, fun x hx i => ?_⟩
  · rw [svec_liftOp]
    by_cases hy : y ∈ G.Ω 1
    · exact ((hsd i).val y hy).trans hmono
    · rw [zeroExt_not_mem _ _ hy, norm_zero, mul_zero]; exact hbC.trans hmono
  · rw [svec_liftOp, svec_liftOp]
    exact ((hsd i).fwd x hx μ).trans hmono
  · rw [svec_liftOp, svec_liftOp]
    by_cases hy : x - Pi.single μ 1 ∈ G.Ω 1
    · have hxy : x - Pi.single μ 1 + Pi.single μ 1 ∈ G.Ω 1 := by simpa using hx
      have h1 := (hsd i).fwd' (x - Pi.single μ 1) hy μ hxy
      simp only [sub_add_cancel] at h1
      have hadj : Adj x (x - Pi.single μ 1) := ⟨μ, Or.inr (by simp)⟩
      have hpd := pathDist_adj_le_one hx hy hadj
      have hw := weight_le_of_pathDist hε hω (by norm_num : (0 : ℝ) ≤ 1) hpd
      rw [norm_sub_rev]
      calc ω x * (G.spacing x * ‖zeroExt (G.Ω 1) (M *ᵥ comp G g i) x -
            zeroExt (G.Ω 1) (M *ᵥ comp G g i) (x - Pi.single μ 1)‖)
          ≤ (Real.exp (ε * 1) * ω (x - Pi.single μ 1)) * (G.spacing x *
            ‖zeroExt (G.Ω 1) (M *ᵥ comp G g i) x -
              zeroExt (G.Ω 1) (M *ᵥ comp G g i) (x - Pi.single μ 1)‖) :=
            mul_le_mul_of_nonneg_right hw (by have := spacing_pos G (x := x); positivity)
        _ = Real.exp ε * (ω (x - Pi.single μ 1) * (G.spacing x *
            ‖zeroExt (G.Ω 1) (M *ᵥ comp G g i) x -
              zeroExt (G.Ω 1) (M *ᵥ comp G g i) (x - Pi.single μ 1)‖)) := by
            rw [mul_one]; ring
        _ ≤ Real.exp ε * (b * C) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hL1 (mul_nonneg (Real.exp_pos ε).le hbC)
          nlinarith
    · rw [zeroExt_not_mem _ _ hy, zero_sub, norm_neg,
        spacing_wall_eq hϱ hL hx hy ⟨μ, Or.inr (by simp)⟩]
      have := (hsd i).val x hx
      calc ω x * ((L : ℝ) * ‖zeroExt (G.Ω 1) (M *ᵥ comp G g i) x‖)
          = L * (ω x * ‖zeroExt (G.Ω 1) (M *ᵥ comp G g i) x‖) := by ring
        _ ≤ L * (b * C) := mul_le_mul_of_nonneg_left this (by linarith)
        _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hE1 (mul_nonneg (by linarith : (0 : ℝ) ≤ L) hbC)
          nlinarith
  · rw [svec_liftOp]
    have := (hsd i).lap x hx
    refine le_trans (le_of_eq ?_) (this.trans hmono)
    simp only [svec_liftOp]


/-- **A field with weighted value, forward gradient and Laplacian bounds** has the four weighted
bounds, with the backward gradient and the wall bonds costing `L e^ε`. -/
theorem wsup_of_fwd (hϱ : 1 < ϱ) (hL : 2 ≤ L) {ε : ℝ} (hε : 0 ≤ ε)
    {ω : CTorus d L N₁ m₁ K → ℝ} (hω : IsWeight G ε ω) {u : G.Ω 1 × Fin N → ℂ} {V : ℝ}
    (hV : 0 ≤ V) (hval : ∀ (y : CTorus d L N₁ m₁ K) (i : Fin N), ω y * ‖svec G u y i‖ ≤ V)
    (hfwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N), ω x * (G.spacing x *
      ‖svec G u (x + Pi.single μ 1) i - svec G u x i‖) ≤ V)
    (hlap : ∀ x ∈ G.Ω 1, ∀ i : Fin N, ω x * (G.spacing x ^ 2 * ‖∑ μ : Fin d, (2 * svec G u x i -
      svec G u (x + Pi.single μ 1) i - svec G u (x - Pi.single μ 1) i)‖) ≤ V) :
    WSup G ω u (L * Real.exp ε * V) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hE1 : 1 ≤ Real.exp ε := Real.one_le_exp hε
  have hLE : 1 ≤ (L : ℝ) * Real.exp ε := one_le_mul_of_one_le_of_one_le hL1 hE1
  have hmono : V ≤ L * Real.exp ε * V := le_mul_of_one_le_left hV hLE
  refine ⟨fun y i => (hval y i).trans hmono, fun x hx μ i => (hfwd x hx μ i).trans hmono,
    fun x hx μ i => ?_, fun x hx i => (hlap x hx i).trans hmono⟩
  by_cases hy : x - Pi.single μ 1 ∈ G.Ω 1
  · have h1 := hfwd (x - Pi.single μ 1) hy μ i
    simp only [sub_add_cancel] at h1
    have hadj : Adj x (x - Pi.single μ 1) := ⟨μ, Or.inr (by simp)⟩
    have hpd := pathDist_adj_le_one hx hy hadj
    have hw := weight_le_of_pathDist hε hω (by norm_num : (0 : ℝ) ≤ 1) hpd
    have hsp := spacing_adj_le G hϱ.le hy hx (Adj.symm hadj)
    rw [norm_sub_rev] at h1
    have hs0 := (spacing_pos G (x := x - Pi.single μ 1)).le
    have hn := norm_nonneg (svec G u (x - Pi.single μ 1) i - svec G u x i)
    calc ω x * (G.spacing x * ‖svec G u (x - Pi.single μ 1) i - svec G u x i‖)
        ≤ (Real.exp (ε * 1) * ω (x - Pi.single μ 1)) *
          ((L * G.spacing (x - Pi.single μ 1)) * ‖svec G u (x - Pi.single μ 1) i - svec G u x i‖) := by
          refine mul_le_mul hw (mul_le_mul_of_nonneg_right hsp hn)
            (mul_nonneg (spacing_pos G (x := x)).le hn)
            (mul_nonneg (Real.exp_pos _).le (le_trans zero_le_one (hω.1 _)))
      _ = (L * Real.exp ε) * (ω (x - Pi.single μ 1) * (G.spacing (x - Pi.single μ 1) *
          ‖svec G u (x - Pi.single μ 1) i - svec G u x i‖)) := by rw [mul_one]; ring
      _ ≤ (L * Real.exp ε) * V := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := hfwd (x - Pi.single μ 1) hy μ i
          simp only [sub_add_cancel] at this
          rw [norm_sub_rev] at this
          exact this
  · have hz : svec G u (x - Pi.single μ 1) i = 0 := svec_of_not_mem G u hy i
    rw [hz, zero_sub, norm_neg, spacing_wall_eq hϱ hL hx hy ⟨μ, Or.inr (by simp)⟩]
    calc ω x * ((L : ℝ) * ‖svec G u x i‖) = L * (ω x * ‖svec G u x i‖) := by ring
      _ ≤ L * V := mul_le_mul_of_nonneg_left (by simpa using hval x i) (by linarith)
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hE1 (mul_nonneg (by linarith : (0 : ℝ) ≤ L) hV)
        nlinarith

end WSup

section Specs

variable {d L : ℕ} [NeZero L]

/-- The conclusion of `dg2_sup` (weighted pointwise bounds of `G_s`) with the constants
`(c, B_G)`. -/
def Dg2Spec (d L : ℕ) [NeZero L] (cstar BG : ℝ) : Prop :=
  0 ≤ cstar ∧ 0 ≤ BG ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × CTorus d L N₁ m₁ K → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {w : CTorus d L N₁ m₁ K → ℝ}, IsWeight G (gammaW d) w →
      ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      IsUnit (1 - Kcal G a ν α s) ∧
      SupBdW G w (zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f)) (BG * Real.exp (N0 d L * κ) * C)

theorem Dg2Spec.mono {c c' BG BG' : ℝ} (h : Dg2Spec d L c BG) (hc : c ≤ c') (hB : BG ≤ BG') :
    Dg2Spec d L c' BG' := by
  refine ⟨h.1.trans hc, h.2.1.trans hB, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα κ hκ hM s hs w hw f C hC hf
  obtain ⟨hU, hS⟩ := h.2.2 G S hα hκ
    (le_trans (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le) hM) hs hw f hC hf
  exact ⟨hU, hS.mono (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le) hC)⟩

theorem dg2Spec_exists (hd : 3 ≤ d) (hL : 3 ≤ L) : ∃ c BG : ℝ, Dg2Spec d L c BG := by
  obtain ⟨c, B, hc, hB, H⟩ := dg2_sup (d := d) (L := L) hd hL
  refine ⟨c, B, hc, hB, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα κ hκ hM s hs w hw f C hC hf
  exact H G S hα hκ hM hs hw f hC hf

/-- The conclusion of `dg6` (closeness of `G_s` to `G_D` away from `W`) with the constants
`(c, B_G)`. -/
def CloseSpec (d L : ℕ) [NeZero L] (cstar BG : ℝ) : Prop :=
  0 ≤ cstar ∧ 0 ≤ BG ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × CTorus d L N₁ m₁ K → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {W : Finset (CTorus d L N₁ m₁ K)},
      (∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) →
      ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      ∀ x ∈ G.Ω 1,
      ‖Gdiff G a ν α s f x‖ ≤ BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist G W x) * C ∧
      (∀ μ : Fin d, G.spacing x * ‖Gdiff G a ν α s f (x + Pi.single μ 1) -
        Gdiff G a ν α s f x‖ ≤
        BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist G W x) * C) ∧
      (G.spacing x) ^ 2 * ‖∑ μ : Fin d, (2 * Gdiff G a ν α s f x -
        Gdiff G a ν α s f (x + Pi.single μ 1) - Gdiff G a ν α s f (x - Pi.single μ 1))‖ ≤
        BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist G W x) * C

theorem CloseSpec.mono {c c' BG BG' : ℝ} (h : CloseSpec d L c BG) (hc : c ≤ c') (hB : BG ≤ BG') :
    CloseSpec d L c' BG' := by
  refine ⟨h.1.trans hc, h.2.1.trans hB, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα κ hκ hM s hs W hW f C hC hf x hx
  have hM' : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ :=
    le_trans (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le) hM
  obtain ⟨h1, h2, h3⟩ := h.2.2 G S hα hκ hM' hs hW f hC hf x hx
  have hmono : BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist G W x) * C ≤
      BG' * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist G W x) * C := by
    have := decay_nonneg (gammaW d) (siteSetDist G W x)
    have := (Real.exp_pos (N0 d L * κ)).le
    gcongr
  exact ⟨h1.trans hmono, fun μ => (h2 μ).trans hmono, h3.trans hmono⟩

theorem closeSpec_exists (hd : 3 ≤ d) (hL : 3 ≤ L) : ∃ c BG : ℝ, CloseSpec d L c BG := by
  obtain ⟨c, B, hc, hB, H⟩ := dg6 (d := d) (L := L) hd hL
  refine ⟨c, B, hc, hB, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα κ hκ hM s hs W hW f C hC hf x hx
  exact H G S hα hκ hM hs hW f hC hf x hx


/-- **One set of constants for all the inputs of Theorem I-4a.** -/
theorem specs_exist (hd : 3 ≤ d) (hL : 3 ≤ L) : ∃ c BG : ℝ, FamSpec d L c BG ∧ Dg2Spec d L c BG ∧
    CloseSpec d L c BG ∧ OneSpec d L c ∧ AnSpec d L c := by
  obtain ⟨c1, B1, h1⟩ := decGreenFamily (d := d) (L := L) hd hL
  obtain ⟨c2, B2, h2⟩ := dg2Spec_exists (d := d) (L := L) hd hL
  obtain ⟨c3, B3, h3⟩ := closeSpec_exists (d := d) (L := L) hd hL
  obtain ⟨c4, h4⟩ := oneSpec_exists (d := d) (L := L) hd hL
  obtain ⟨c5, h5⟩ := anSpec_exists (d := d) (L := L) hd hL
  set c := max (max (max (max c1 c2) c3) c4) c5 with hc
  set B := max (max B1 B2) B3 with hB
  refine ⟨c, B, (h1.mono_c ?_).mono_BG ?_, h2.mono ?_ ?_, h3.mono ?_ ?_, h4.mono_c ?_, h5.mono_c ?_⟩
  all_goals simp [hc, hB]

end Specs

section Close

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem wgt_mul_decay (W : Finset (CTorus d L N₁ m₁ K)) (t : ℝ) {γ : ℝ} (hγ : 0 ≤ γ)
    (y : CTorus d L N₁ m₁ K) :
    wgt G W t γ y * decay γ (siteSetDist G W y) ≤ 1 := by
  by_cases h : siteSetDist G W y = ⊤
  · rw [h, decay_top, mul_zero]; exact zero_le_one
  · rw [decay_of_ne_top h]
    unfold wgt
    rw [← Real.exp_add, Real.exp_le_one_iff]
    have : (truncSetDist G W t y).toReal ≤ (siteSetDist G W y).toReal :=
      ENNReal.toReal_mono h (min_le_left _ _)
    nlinarith

/-- **The part of `δφ(s) - δφ(1)` coming from `G_s - G_D`** (via `dg6`): weighted bounds with the
weight `e^{γ_w min(d(x, W), t)}`. -/
theorem wsup_close {c BG6 : ℝ} (hC : CloseSpec d L c BG6) (S : DGSetting G a ν)
    {α : G.Ω 1 → ℂ} (hα : AdmPot G α) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    {W : Finset (CTorus d L N₁ m₁ K)} (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W)
    (g : G.Ω 1 × Fin N → ℂ) {C : ℝ} (hCn : 0 ≤ C) (hg : SrcBound G g C) {t : ℝ} :
    WSup G (wgt G W t (gammaW d)) (liftOp N (Gs G a ν α s) *ᵥ g -
        liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g)
      (L * Real.exp (gammaW d) * (BG6 * Real.exp (N0 d L * κ) * C)) := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hγ := gammaW_nonneg hd0
  have hB6 : 0 ≤ BG6 * Real.exp (N0 d L * κ) * C := by
    have := hC.2.1; positivity
  have hω := isWeight_wgt (G := G) W t hγ
  refine wsup_of_fwd S.one_lt_rho (by have := S.hL; omega) hγ hω hB6 ?_ ?_ ?_
  · intro y i
    rw [svec_liftOp_sub]
    by_cases hy : y ∈ G.Ω 1
    · obtain ⟨h1, -, -⟩ := hC.2.2 G S hα hκ hM hs hW (comp G g i) hCn (fun x => hg x i) y hy
      have e : zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ comp G g i) y -
          zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ comp G g i) y =
          Gdiff G a ν α s (comp G g i) y := rfl
      rw [e]
      have hw := wgt_mul_decay (G := G) W t hγ y
      have hbc : 0 ≤ BG6 * Real.exp (N0 d L * κ) * C := hB6
      calc wgt G W t (gammaW d) y * ‖Gdiff G a ν α s (comp G g i) y‖
          ≤ wgt G W t (gammaW d) y * (BG6 * Real.exp (N0 d L * κ) *
            decay (gammaW d) (siteSetDist G W y) * C) :=
            mul_le_mul_of_nonneg_left h1 (wgt_pos W t _ y).le
        _ = (wgt G W t (gammaW d) y * decay (gammaW d) (siteSetDist G W y)) *
            (BG6 * Real.exp (N0 d L * κ) * C) := by ring
        _ ≤ 1 * (BG6 * Real.exp (N0 d L * κ) * C) := mul_le_mul_of_nonneg_right hw hbc
        _ = _ := one_mul _
    · rw [zeroExt_not_mem _ _ hy, zeroExt_not_mem _ _ hy, sub_zero, norm_zero, mul_zero]
      exact hB6
  · intro x hx μ i
    simp only [svec_liftOp_sub]
    obtain ⟨-, h2, -⟩ := hC.2.2 G S hα hκ hM hs hW (comp G g i) hCn (fun x => hg x i) x hx
    have e : ∀ y : CTorus d L N₁ m₁ K, zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ comp G g i) y -
          zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ comp G g i) y =
          Gdiff G a ν α s (comp G g i) y := fun y => rfl
    simp only [e]
    have hw := wgt_mul_decay (G := G) W t hγ x
    calc wgt G W t (gammaW d) x * (G.spacing x * ‖Gdiff G a ν α s (comp G g i) (x + Pi.single μ 1) -
          Gdiff G a ν α s (comp G g i) x‖)
        ≤ wgt G W t (gammaW d) x * (BG6 * Real.exp (N0 d L * κ) *
            decay (gammaW d) (siteSetDist G W x) * C) :=
            mul_le_mul_of_nonneg_left (h2 μ) (wgt_pos W t _ x).le
      _ = (wgt G W t (gammaW d) x * decay (gammaW d) (siteSetDist G W x)) *
          (BG6 * Real.exp (N0 d L * κ) * C) := by ring
      _ ≤ 1 * (BG6 * Real.exp (N0 d L * κ) * C) := mul_le_mul_of_nonneg_right hw hB6
      _ = _ := one_mul _
  · intro x hx i
    simp only [svec_liftOp_sub]
    obtain ⟨-, -, h3⟩ := hC.2.2 G S hα hκ hM hs hW (comp G g i) hCn (fun x => hg x i) x hx
    have e : ∀ y : CTorus d L N₁ m₁ K, zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ comp G g i) y -
          zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ comp G g i) y =
          Gdiff G a ν α s (comp G g i) y := fun y => rfl
    simp only [e]
    have hw := wgt_mul_decay (G := G) W t hγ x
    calc wgt G W t (gammaW d) x * (G.spacing x ^ 2 * ‖∑ μ : Fin d,
          (2 * Gdiff G a ν α s (comp G g i) x - Gdiff G a ν α s (comp G g i) (x + Pi.single μ 1) -
            Gdiff G a ν α s (comp G g i) (x - Pi.single μ 1))‖)
        ≤ wgt G W t (gammaW d) x * (BG6 * Real.exp (N0 d L * κ) *
            decay (gammaW d) (siteSetDist G W x) * C) :=
            mul_le_mul_of_nonneg_left h3 (wgt_pos W t _ x).le
      _ = (wgt G W t (gammaW d) x * decay (gammaW d) (siteSetDist G W x)) *
          (BG6 * Real.exp (N0 d L * κ) * C) := by ring
      _ ≤ 1 * (BG6 * Real.exp (N0 d L * κ) * C) := mul_le_mul_of_nonneg_right hw hB6
      _ = _ := one_mul _


/-- **The weighted bounds of `G_D(A) g`** for a weighted source `g` (from `dg2_sup` at `s = 1`). -/
theorem wsup_green {c BG : ℝ} (hD : Dg2Spec d L c BG) (h1 : OneSpec d L c) (S : DGSetting G a ν)
    (hM0 : c ≤ (L : ℝ) ^ m₁) {A : G.Ω 1 → ℂ} (hA : AdmPot G A)
    {ω : CTorus d L N₁ m₁ K → ℝ} (hω : IsWeight G (gammaW d) ω)
    (g : G.Ω 1 × Fin N → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ (x : G.Ω 1) (i : Fin N), ω x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
      ‖g (x, i)‖ ≤ C) :
    WSup G ω (liftOp N (dirichletOperator G a ν A)⁻¹ *ᵥ g) (L * Real.exp (gammaW d) * (BG * C)) := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hγ := gammaW_nonneg hd0
  have hone : Gs G a ν A (fun _ => 1) = (dirichletOperator G a ν A)⁻¹ := (h1.2 G S hA hM0).2
  have hM00 : c * Real.exp (N0 d L * 0) ≤ (L : ℝ) ^ m₁ := by simpa using hM0
  refine wsup_liftOp S.one_lt_rho (by have := S.hL; omega) hγ hω hD.2.1 (fun f C' hC' hf => ?_)
    g hC hg
  have := (hD.2.2 G S hA (κ := 0) le_rfl hM00 (s := fun _ => 1) (by simp) hω f hC' hf).2
  rw [hone] at this
  simpa using this


/-- **The resolvent identity for vector fields**:
`(Ĝ(A) - Ĝ(A')) F = Ĝ(A) (-(A - A') Ĝ(A') F)`. -/
theorem green_sub_vec (S : DGSetting G a ν) {A A' : G.Ω 1 → ℂ} (hA : AdmPot G A)
    (hA' : AdmPot G A') (F : G.Ω 1 × Fin N → ℂ) :
    liftOp N (dirichletOperator G a ν A)⁻¹ *ᵥ F - liftOp N (dirichletOperator G a ν A')⁻¹ *ᵥ F =
      liftOp N (dirichletOperator G a ν A)⁻¹ *ᵥ
        (fun p => -(A p.1 - A' p.1) * (liftOp N (dirichletOperator G a ν A')⁻¹ *ᵥ F) p) := by
  have hd0 : 0 < d := by have := S.hd; omega
  funext ⟨x, i⟩
  rw [Pi.sub_apply, liftOp_mulVec, liftOp_mulVec, liftOp_mulVec]
  have := congrFun (green_sub_eq_mulVec G hd0 S.mass S.weights A A' hA hA' (fun z => F (z, i))) x
  rw [Pi.sub_apply] at this
  rw [this]
  congr 1
  funext y
  rw [liftOp_mulVec]

theorem vec_telescope {M M0 M' : Matrix (G.Ω 1) (G.Ω 1) ℂ} (F F' : G.Ω 1 × Fin N → ℂ) :
    liftOp N M *ᵥ F - liftOp N M' *ᵥ F' =
      (liftOp N M *ᵥ F - liftOp N M0 *ᵥ F) + liftOp N M0 *ᵥ (F - F') +
        (liftOp N M0 *ᵥ F' - liftOp N M' *ᵥ F') := by
  rw [Matrix.mulVec_sub]
  abel


/-- The factor `e^{2 d γ_w}` by which a weight of rate `γ_w` changes over a site, its neighbours
and its block. -/
noncomputable def wFac (d : ℕ) : ℝ := Real.exp (gammaW d * (2 * d))

theorem wFac_ge_one (d : ℕ) (hd : 0 < d) : 1 ≤ wFac d := by
  unfold wFac; exact Real.one_le_exp (by have := gammaW_nonneg hd; positivity)

/-- The smallness constant of the closeness estimate. -/
noncomputable def closeLam (d L N : ℕ) [NeZero L] (B : ℝ) : ℝ :=
  N * cF d L + commKConst d L N * wFac d + N * (2 * d + 8) * wFac d * cK2' d L N B

noncomputable def closeM0 (d L N : ℕ) [NeZero L] (BG B : ℝ) : ℝ :=
  L * Real.exp (gammaW d) * BG * (3 / 2 + cK2' d L N B)

/-- The smallness of `δ₀, δ₁` under which the closeness estimate holds. -/
noncomputable def deltaClose (d L N : ℕ) [NeZero L] (BG κ : ℝ) : ℝ :=
  min (deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (min 1 (min (1 / (2 * closeLam d L N (famConst d L BG κ) *
      closeM0 d L N BG (famConst d L BG κ) + 1))
      (1 / (2 * closeLam d L N (famConst d L BG κ) + 1))))

/-- The constant of the closeness estimate: `L e^{γ_w} B_G e^{N₀κ₁} (C_F + (3/2) K₂) δ₁`. -/
noncomputable def closeConst (d L N : ℕ) [NeZero L] (BG κ δ₁ : ℝ) : ℝ :=
  L * Real.exp (gammaW d) * (BG * Real.exp (N0 d L * κ) *
    ((cF d L + 3 / 2 * cK2' d L N (famConst d L BG κ)) * δ₁))

omit [NeZero L] in
theorem cK2'_nonneg {B : ℝ} (hB0 : 0 ≤ B) : 0 ≤ cK2' d L N B := by
  have h1 := cN'_pos (d := d) (L := L) (N := N) hB0
  have h2 := Balaban.Background.cF_pos d L
  unfold cK2'; positivity

theorem closeLam_nonneg {B : ℝ} (hB0 : 0 ≤ B) (hd : 0 < d) : 0 ≤ closeLam d L N B := by
  have h1 := cK2'_nonneg (d := d) (L := L) (N := N) hB0
  have h2 := Balaban.Background.cF_pos d L
  have h3 := wFac_ge_one d hd
  have h3' : 0 ≤ wFac d := by linarith
  unfold closeLam commKConst; positivity

theorem closeM0_nonneg {BG B : ℝ} (hBG : 0 ≤ BG) (hB0 : 0 ≤ B) :
    0 ≤ closeM0 d L N BG B := by
  have h1 := cK2'_nonneg (d := d) (L := L) (N := N) hB0
  unfold closeM0; positivity


theorem close_arith {Λ M Va E : ℝ} (hM : 0 ≤ M) (hVa : 0 ≤ Va) (hΛM : 2 * Λ * M ≤ 1)
    (hΛ1 : 2 * Λ ≤ 1) (hE : E ≤ Λ * (Va + M * E)) (hE0 : 0 ≤ E) :
    E ≤ Va ∧ Va + M * E ≤ 2 * Va := by
  have h1 : E ≤ 2 * Λ * Va := by
    have : Λ * M * E ≤ E / 2 := by nlinarith
    nlinarith
  refine ⟨h1.trans ?_, ?_⟩
  · nlinarith
  · have : M * E ≤ M * (2 * Λ * Va) := mul_le_mul_of_nonneg_left h1 hM
    nlinarith

theorem extS_norm_le {κ : ℝ} (hκ : 0 ≤ κ) {s : DecParams G} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) :
    ∀ P, ‖extS G s P‖ ≤ Real.exp κ := by
  intro P
  unfold extS
  split_ifs with h
  · exact hs ⟨P, h⟩
  · simpa using Real.one_le_exp hκ

theorem close_smallness {lam m0 dc Λ M : ℝ} (hlam : 0 ≤ lam) (hm0 : 0 ≤ m0)
    (hM0 : 0 ≤ M) (hΛ : Λ ≤ lam * dc) (hM : M ≤ m0) (hdc0 : 0 ≤ dc)
    (hdc2 : dc ≤ 1 / (2 * lam * m0 + 1)) (hdc3 : dc ≤ 1 / (2 * lam + 1)) :
    2 * Λ * M ≤ 1 ∧ 2 * Λ ≤ 1 := by
  have h2 : dc * (2 * lam * m0 + 1) ≤ 1 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * lam * m0 + 1)).1 hdc2
    exact this
  have h3 : dc * (2 * lam + 1) ≤ 1 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * lam + 1)).1 hdc3
  constructor
  · have : Λ * M ≤ (lam * dc) * m0 := mul_le_mul hΛ hM hM0 (by positivity)
    nlinarith [mul_nonneg hlam hm0, mul_nonneg hdc0 (mul_nonneg hlam hm0)]
  · nlinarith [mul_nonneg hdc0 hlam]

/-- **The three pieces of `δφ(s) - δφ(1)`** (Step 4 of I-4a): the source term `G_s - G_D`
(`dg6`), the linear term in the difference of the potentials and the resolvent term
(`G_D(A) - G_D(A') = -G_D(A)(A - A')G_D(A')`). -/
theorem close_pieces {c BG : ℝ} (hD : Dg2Spec d L c BG) (hCl : CloseSpec d L c BG)
    (h1 : OneSpec d L c) (S : DGSetting G a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hM0 : c ≤ (L : ℝ) ^ m₁)
    {s : DecParams G} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {W : Finset (CTorus d L N₁ m₁ K)}
    (hW : ∀ z ∈ cubeIdx G, sProd G (extS G s) z ≠ 1 → intBox z ⊆ W) (t : ℝ)
    {α₀ : G.Ω 1 → ℂ} {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ} {Fs : G.Ω 1 × Fin N → ℂ}
    {δα δα' : G.Ω 1 → ℂ} {CF X E : ℝ} (hCF0 : 0 ≤ CF) (hX0 : 0 ≤ X) (hE0 : 0 ≤ E)
    (hAdm : AdmPot G (α₀ + δα)) (hAdm' : AdmPot G (α₀ + δα'))
    (hF₀ : SrcBound G (Fsrc φ₀ Fs δα) CF) (hphi : ∀ x ∈ G.Ω 1, vn (φ₀ x) ≤ 3 / 2)
    (he : ∀ x : G.Ω 1, wgt G W t (gammaW d) x *
      (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖) ≤ E)
    (hdp' : SupBounds G (dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ Fs δα') X) :
    WSup G (wgt G W t (gammaW d))
      (dphi G (decG G a ν s) α₀ φ₀ Fs δα - dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ Fs δα')
      (L * Real.exp (gammaW d) * (BG * Real.exp (N0 d L * κ) * CF) +
        L * Real.exp (gammaW d) * (BG * (3 / 2 * E)) +
        L * Real.exp (gammaW d) * (BG * (E * X))) := by
  classical
  have hd0 : 0 < d := by have := S.hd; omega
  have hγ := gammaW_nonneg hd0
  have hBG : 0 ≤ BG := hD.2.1
  set ω : CTorus d L N₁ m₁ K → ℝ := wgt G W t (gammaW d) with hωdef
  have hω : IsWeight G (gammaW d) ω := isWeight_wgt W t hγ
  have hω0 : ∀ y, 0 ≤ ω y := fun y => (wgt_pos W t _ y).le
  set F₀ : G.Ω 1 × Fin N → ℂ := Fsrc φ₀ Fs δα with hF₀def
  set F₁ : G.Ω 1 × Fin N → ℂ := Fsrc φ₀ Fs δα' with hF₁def
  have hs' := extS_norm_le hκ hs
  have Ta := wsup_close (G := G) hCl S hAdm hκ hM hs' hW F₀ hCF0 hF₀ (t := t)
  have hdiffsrc : ∀ (x : G.Ω 1) (i : Fin N), ω x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
      ‖(F₀ - F₁) (x, i)‖ ≤ 3 / 2 * E := by
    intro x i
    have hphi' : ‖φ₀ x i‖ ≤ 3 / 2 := (norm_le_vn _ i).trans (hphi x x.2)
    have e2 : (F₀ - F₁) (x, i) = -((δα x - δα' x) * φ₀ x i) := by
      simp only [hF₀def, hF₁def, Fsrc, Pi.sub_apply]; ring
    rw [e2, norm_neg, norm_mul]
    calc ω x * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * (‖δα x - δα' x‖ * ‖φ₀ x i‖)
        = (ω x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖)) * ‖φ₀ x i‖ := by ring
      _ ≤ E * (3 / 2) := mul_le_mul (he x) hphi' (norm_nonneg _) hE0
      _ = _ := by ring
  have Tb := wsup_green (G := G) hD h1 S hM0 hAdm hω (F₀ - F₁) (by positivity) hdiffsrc
  have hone' : decG G a ν (fun _ => 1) (α₀ + δα') = (dirichletOperator G a ν (α₀ + δα'))⁻¹ :=
    decG_one h1 S hM0 hAdm'
  have hsrcc : ∀ (x : G.Ω 1) (i : Fin N), ω x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
      ‖(fun p : G.Ω 1 × Fin N => -((α₀ + δα) p.1 - (α₀ + δα') p.1) *
        (liftOp N (dirichletOperator G a ν (α₀ + δα'))⁻¹ *ᵥ F₁) p) (x, i)‖ ≤ E * X := by
    intro x i
    have hv : ‖(liftOp N (dirichletOperator G a ν (α₀ + δα'))⁻¹ *ᵥ F₁) (x, i)‖ ≤ X := by
      have h2 := hdp'.val x i
      rw [svec_of_mem] at h2
      have : dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ Fs δα' =
          liftOp N (dirichletOperator G a ν (α₀ + δα'))⁻¹ *ᵥ F₁ := by
        unfold dphi; rw [hone']
      rwa [this] at h2
    simp only [norm_mul, norm_neg]
    have e3 : (α₀ + δα) x - (α₀ + δα') x = δα x - δα' x := by simp
    rw [e3]
    calc ω x * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
          (‖δα x - δα' x‖ * ‖(liftOp N (dirichletOperator G a ν (α₀ + δα'))⁻¹ *ᵥ F₁) (x, i)‖)
        = (ω x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖)) *
          ‖(liftOp N (dirichletOperator G a ν (α₀ + δα'))⁻¹ *ᵥ F₁) (x, i)‖ := by ring
      _ ≤ E * X := mul_le_mul (he x) hv (norm_nonneg _) hE0
  have Tc := wsup_green (G := G) hD h1 S hM0 hAdm hω
    (fun p : G.Ω 1 × Fin N => -((α₀ + δα) p.1 - (α₀ + δα') p.1) *
      (liftOp N (dirichletOperator G a ν (α₀ + δα'))⁻¹ *ᵥ F₁) p) (by positivity) hsrcc
  have hsum : dphi G (decG G a ν s) α₀ φ₀ Fs δα -
      dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ Fs δα' =
      (liftOp N (Gs G a ν (α₀ + δα) (extS G s)) *ᵥ F₀ -
        liftOp N (dirichletOperator G a ν (α₀ + δα))⁻¹ *ᵥ F₀) +
      liftOp N (dirichletOperator G a ν (α₀ + δα))⁻¹ *ᵥ (F₀ - F₁) +
      liftOp N (dirichletOperator G a ν (α₀ + δα))⁻¹ *ᵥ
        (fun p : G.Ω 1 × Fin N => -((α₀ + δα) p.1 - (α₀ + δα') p.1) *
          (liftOp N (dirichletOperator G a ν (α₀ + δα'))⁻¹ *ᵥ F₁) p) := by
    have e1' : dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ Fs δα' =
        liftOp N (dirichletOperator G a ν (α₀ + δα'))⁻¹ *ᵥ F₁ := by
      unfold dphi; rw [hone']
    rw [e1', ← green_sub_vec S hAdm hAdm' F₁]
    exact vec_telescope (M0 := (dirichletOperator G a ν (α₀ + δα))⁻¹) F₀ F₁
  rw [hsum]
  exact (Ta.add hω0 Tb).add hω0 Tc

/-- **The weighted bound for the difference of the potentials** from the weighted bounds of the
difference of the fields (`δα = 𝒩(δφ)` at both parameters). -/
theorem close_nmap {ιU : Bool} {α₀ : G.Ω 1 → ℂ}
    {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} {f₁ : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (H : DecHyp G a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁) {s : DecParams G}
    {δα δα' : G.Ω 1 → ℂ}
    (hfix : DecFixed G a ν s ιU α₀ φ₀ (pertSource G a δΨ f₁) δα)
    (hfix' : DecFixed G a ν (fun _ => 1) ιU α₀ φ₀ (pertSource G a δΨ f₁) δα')
    {X V : ℝ} (hX0 : 0 ≤ X) (hV0 : 0 ≤ V)
    (hstar : StarBound G (dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα) X)
    (hstar' : StarBound G (dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα') X)
    {W : Finset (CTorus d L N₁ m₁ K)} {t : ℝ}
    (hWS : WSup G (wgt G W t (gammaW d))
      (dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα -
        dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα') V)
    (x : G.Ω 1) :
    wgt G W t (gammaW d) x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖) ≤
      (N * (cF d L * δ₁) + commKConst d L N * δ₀ * wFac d + N * (2 * d + 8) * wFac d * X) * V := by
  have hd0 : 0 < d := by have := H.green.hd; omega
  have hγ := gammaW_nonneg hd0
  have hω : IsWeight G (gammaW d) (wgt G W t (gammaW d)) := isWeight_wgt W t hγ
  have hFsb : SrcBound G (pertSource G a δΨ f₁) (cF d L * δ₁) :=
    pertSource_bound H.green H.δ₁_nn H.dPsi H.f₁_bd
  have hN := Nmap_diff_weighted (G := G) (a := a) (ν := ν) (ιU := ιU) H.green (α₀ := α₀)
    (φ₀ := φ₀) (Fs := pertSource G a δΨ f₁) H.smooth H.δ₀_nn hFsb (x := x)
    ((H.alpha0 x).trans H.δ₀_le) hγ hω (E := V) hV0 hX0 hX0 hstar hstar' hWS.val
    (fun μ i => hWS.fwd x x.2 μ i) (fun μ i => hWS.bwd x x.2 μ i)
  have hx1 := congrFun hfix x
  have hx2 := congrFun hfix' x
  have : wgt G W t (gammaW d) x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖) =
      wgt G W t (gammaW d) x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
        ‖Nmap G (dirichletOperator G a ν α₀) ιU φ₀ (pertSource G a δΨ f₁)
            (dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα) x -
          Nmap G (dirichletOperator G a ν α₀) ιU φ₀ (pertSource G a δΨ f₁)
            (dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα') x‖) := by
    rw [hx1, hx2]
  rw [this]
  refine hN.trans (le_of_eq ?_)
  unfold wFac; ring



/-- **Theorem I-4a (d), the estimate.**  The solutions at `s` and at `s ≡ 1` differ by a weighted
amount of the size of the source `G_s - G_D`, with the weight `e^{γ_w min(d(·, W), t)}`. -/
theorem i4a_close_core {c BG : ℝ} (hF : FamSpec d L c BG) (hD : Dg2Spec d L c BG)
    (hCl : CloseSpec d L c BG) (h1 : OneSpec d L c) (S : DGSetting G a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams G}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {W : Finset (CTorus d L N₁ m₁ K)}
    (hW : ∀ z ∈ cubeIdx G, sProd G (extS G s) z ≠ 1 → intBox z ⊆ W)
    {ιU : Bool} {α₀ : G.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ} (H : DecHyp G a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaClose d L N BG κ) (hδ₁ : δ₁ ≤ deltaClose d L N BG κ)
    {δα δα' : G.Ω 1 → ℂ}
    (hfix : DecFixed G a ν s ιU α₀ φ₀ (pertSource G a δΨ f₁) δα)
    (hsm : Small G δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : DecFixed G a ν (fun _ => 1) ιU α₀ φ₀ (pertSource G a δΨ f₁) δα')
    (hsm' : Small G δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) (t : ℝ) :
    (∀ x : G.Ω 1, wgt G W t (gammaW d) x *
        (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖) ≤ closeConst d L N BG κ δ₁) ∧
    WSup G (wgt G W t (gammaW d))
      (dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα -
        dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα')
      (2 * closeConst d L N BG κ δ₁) := by
  classical
  have hd0 : 0 < d := by have := S.hd; omega
  have hBG : 0 ≤ BG := hF.2.1
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB0 : 0 ≤ B := by have := famConst_ge_one (L := L) hBG κ hd0; linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hdc : deltaClose d L N BG κ ≤ deltaStar' d L N B Γ := min_le_left _ _
  have hdc1 : deltaClose d L N BG κ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hdc2 : deltaClose d L N BG κ ≤
      1 / (2 * closeLam d L N B * closeM0 d L N BG B + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdc3 : deltaClose d L N BG κ ≤ 1 / (2 * closeLam d L N B + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ₀' : δ₀ ≤ deltaStar' d L N B Γ := hδ₀.trans hdc
  have hδ₁' : δ₁ ≤ deltaStar' d L N B Γ := hδ₁.trans hdc
  have hc0 : 0 ≤ c := hF.1
  have hE1 : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by unfold N0; positivity)
  have hM0 : c ≤ (L : ℝ) ^ m₁ := by nlinarith
  have hs1 : ∀ P : cubeIdx G, ‖(fun _ : cubeIdx G => (1 : ℂ)) P‖ ≤ Real.exp κ := fun P => by
    simpa using Real.one_le_exp hκ
  obtain ⟨δα₀, hfix₀, hs6₀, hsK₀, hdp₀, huniq₀, -⟩ :=
    i4a_exists_unique hF G S hκ hM hs H hδ₀' hδ₁'
  obtain ⟨δα₁, hfix₁, hs6₁, hsK₁, hdp₁, huniq₁, -⟩ :=
    i4a_exists_unique hF G S hκ hM hs1 H hδ₀' hδ₁'
  have e0 : δα = δα₀ := huniq₀ δα hsm hfix
  have e1 : δα' = δα₁ := huniq₁ δα' hsm' hfix'
  set Fs : G.Ω 1 × Fin N → ℂ := pertSource G a δΨ f₁ with hFsdef
  set X : ℝ := cK2' d L N B * δ₁ with hXdef
  have hcK := cK2'_nonneg (d := d) (L := L) (N := N) hB0
  have hX0 : 0 ≤ X := by have := H.δ₁_nn; positivity
  have hsK : Small G δα X := by rw [e0]; exact hsK₀
  have hdp : SupBounds G (dphi G (decG G a ν s) α₀ φ₀ Fs δα) X := by rw [e0]; exact hdp₀
  have hdp' : SupBounds G (dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ Fs δα') X := by
    rw [e1]; exact hdp₁
  have hC' := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ H.δ₀_nn H.δ₁_nn hδ₀' hδ₁'
  have hpoly : δ₀ + c6' d L N B Γ ≤ Γ := by linarith [hC'.poly, hC'.ρ_nn]
  have hAdm : AdmPot G (α₀ + δα) :=
    admPot_of_small hd0 (fun y => ((Small.add H.alpha0 hsm) y).trans hpoly)
  have hAdm' : AdmPot G (α₀ + δα') :=
    admPot_of_small hd0 (fun y => ((Small.add H.alpha0 hsm') y).trans hpoly)
  have hγ := gammaW_nonneg hd0
  have hω0 : ∀ y, 0 ≤ wgt G W t (gammaW d) y := fun y => (wgt_pos W t _ y).le
  set e : G.Ω 1 → ℝ := fun x => wgt G W t (gammaW d) x *
    (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖) with hedef
  have he0 : ∀ x, 0 ≤ e x := fun x => by
    have := spacing_pos G (x := (x : CTorus d L N₁ m₁ K)); have := hω0 x; positivity
  set E : ℝ := ⨆ x, e x with hEdef
  have he_le : ∀ x, e x ≤ E := fun x => le_ciSup (Set.finite_range e).bddAbove x
  have hE0 : 0 ≤ E := Real.iSup_nonneg he0
  set CF : ℝ := cF d L * δ₁ + 3 / 2 * X with hCFdef
  have hCF0 : 0 ≤ CF := by
    have := Balaban.Background.cF_pos d L; have := H.δ₁_nn; positivity
  have hF₀ : SrcBound G (Fsrc φ₀ Fs δα) CF := Fsrc_bd H.setup hsK
  have hWS := close_pieces hD hCl h1 S hκ hM hM0 hs hW t hCF0 hX0 hE0 hAdm hAdm' hF₀ H.phiBd
    he_le hdp'
  set Va : ℝ := closeConst d L N BG κ δ₁ with hVa
  have hVa0 : 0 ≤ Va := by
    have := Balaban.Background.cF_pos d L; have := H.δ₁_nn
    rw [hVa]; unfold closeConst; positivity
  set M : ℝ := L * Real.exp (gammaW d) * BG * (3 / 2 + X) with hMdef
  have hM_0 : 0 ≤ M := by positivity
  have hV₁ : L * Real.exp (gammaW d) * (BG * Real.exp (N0 d L * κ) * CF) +
      L * Real.exp (gammaW d) * (BG * (3 / 2 * E)) + L * Real.exp (gammaW d) * (BG * (E * X)) =
      Va + M * E := by
    rw [hVa, hMdef]; unfold closeConst; rw [hCFdef, hXdef]; ring
  rw [hV₁] at hWS
  set Λ : ℝ := N * (cF d L * δ₁) + commKConst d L N * δ₀ * wFac d +
    N * (2 * d + 8) * wFac d * X with hΛdef
  have hstar : StarBound G (dphi G (decG G a ν s) α₀ φ₀ Fs δα) X :=
    Balaban.Background.SupBounds.star hdp
  have hstar' : StarBound G (dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ Fs δα') X :=
    Balaban.Background.SupBounds.star hdp'
  have hVaME : 0 ≤ Va + M * E := by positivity
  have hall : ∀ x : G.Ω 1, e x ≤ Λ * (Va + M * E) := fun x =>
    close_nmap H hfix hfix' hX0 hVaME hstar hstar' hWS x
  have hw0 : 0 ≤ wFac d := by have := wFac_ge_one d hd0; linarith
  have hcF0 := (Balaban.Background.cF_pos d L).le
  have hKc0 : 0 ≤ commKConst d L N := by unfold commKConst; positivity
  have hΛ0 : 0 ≤ Λ := by
    have := H.δ₀_nn; have := H.δ₁_nn
    rw [hΛdef]; positivity
  have hEΛ : E ≤ Λ * (Va + M * E) := Real.iSup_le hall (mul_nonneg hΛ0 hVaME)
  -- smallness
  have hlam0 := closeLam_nonneg (d := d) (L := L) (N := N) hB0 hd0
  have hm00 := closeM0_nonneg (d := d) (L := L) (N := N) hBG hB0
  have hdc0 : 0 ≤ deltaClose d L N BG κ := by
    have h1' := (deltaStar'_pos (d := d) (L := L) (N := N) hB0 hΓ).le
    have h2' : 0 ≤ 1 / (2 * closeLam d L N B * closeM0 d L N BG B + 1) := by positivity
    have h3' : 0 ≤ 1 / (2 * closeLam d L N B + 1) := by positivity
    exact le_min h1' (le_min zero_le_one (le_min h2' h3'))
  have hΛle : Λ ≤ closeLam d L N B * deltaClose d L N BG κ := by
    have t1 : N * (cF d L * δ₁) ≤ (N * cF d L) * deltaClose d L N BG κ := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hδ₁ (by positivity)
    have t2 : commKConst d L N * δ₀ * wFac d ≤ (commKConst d L N * wFac d) *
        deltaClose d L N BG κ := by
      have := mul_le_mul_of_nonneg_left hδ₀ (mul_nonneg hKc0 hw0)
      calc commKConst d L N * δ₀ * wFac d = commKConst d L N * wFac d * δ₀ := by ring
        _ ≤ _ := this
    have t3 : N * (2 * d + 8) * wFac d * X ≤ (N * (2 * d + 8) * wFac d * cK2' d L N B) *
        deltaClose d L N BG κ := by
      have := mul_le_mul_of_nonneg_left hδ₁ (by positivity :
        (0 : ℝ) ≤ N * (2 * d + 8) * wFac d * cK2' d L N B)
      calc N * (2 * d + 8) * wFac d * X = N * (2 * d + 8) * wFac d * cK2' d L N B * δ₁ := by
            rw [hXdef]; ring
        _ ≤ _ := this
    calc Λ ≤ (N * cF d L) * deltaClose d L N BG κ + (commKConst d L N * wFac d) *
          deltaClose d L N BG κ + (N * (2 * d + 8) * wFac d * cK2' d L N B) *
          deltaClose d L N BG κ := by rw [hΛdef]; exact add_le_add (add_le_add t1 t2) t3
      _ = _ := by unfold closeLam; ring
  have hMle : M ≤ closeM0 d L N BG B := by
    have hX1 : X ≤ cK2' d L N B := by
      rw [hXdef]
      calc cK2' d L N B * δ₁ ≤ cK2' d L N B * 1 :=
            mul_le_mul_of_nonneg_left (hδ₁.trans hdc1) hcK
        _ = _ := mul_one _
    unfold closeM0
    rw [hMdef]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  obtain ⟨hs2M, hs2⟩ := close_smallness hlam0 hm00 hM_0 hΛle hMle hdc0 hdc2 hdc3
  obtain ⟨hEVa, hVE⟩ := close_arith hM_0 hVa0 hs2M hs2 hEΛ hE0
  exact ⟨fun x => (he_le x).trans hEVa, hWS.mono hVE⟩

end Close

end Balaban.Localization
