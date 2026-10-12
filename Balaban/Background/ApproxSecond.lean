/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ApproxField
public import Balaban.Background.WeightsMixed
public import Balaban.Background.NormalizeMixed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# All second differences of the approximate field (extension of Lemma 5.3 (A3))

For the approximate field `φ₀ = approxField` and every site `y` of layer `n ≥ 2` (so that `y` and
its neighbours lie in `Ω₁`), the unit-square mixed second difference
`φ₀(y+e_μ+e_τ) - φ₀(y+e_μ) - φ₀(y+e_τ) + φ₀(y)` (all pairs `μ, τ`, including `μ = τ`; the other
sign patterns are the same expression at another base site) is at most `C δ / ℓ(y)²`,
`ℓ(y) = L^n`, with `C = cMix d L` depending on `(d, L)` only (`phi0_sq`).

For `n ≥ 3` it is obtained from the four-point bounds `normalize_mixed`, `interp_sq_le`; for
`n = 2` from the crude bond bound `phi0_adj_close`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Closeness

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν δ ε : ℝ} {D : BgData G N}

/-- The data at adjacent sites of `Ω₁ ∪ C` (the first in `Ω₁`) differ by at most `2 δ`. -/
theorem Ψ_close_adj (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    {y z : Torus d (N₀ * L ^ k)} (hy : y ∈ G.Ω 1) (hadj : Adj y z) :
    cNorm (D.Ψ z - D.Ψ y) ≤ 2 * δ := by
  obtain ⟨l1, l2⟩ := adj_layers S.hϱ S.hd S.hL hy hadj
  have := Ψ_adj_close W ((mem_dataSites G).2 (Or.inl hy)) (mem_dataSites_of_adj hy hadj) hadj
    l1 l2
  have e : cNorm (D.Ψ z - D.Ψ y) = cNorm (D.Ψ y - D.Ψ z) := vn_sub_comm _ _
  linarith

/-- Two adjacent steps from a site of `Ω₁` through a site of `Ω₁`. -/
theorem Ψ_close_adj2 (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    {y z₁ z : Torus d (N₀ * L ^ k)} (hy : y ∈ G.Ω 1) (hz₁ : z₁ ∈ G.Ω 1) (h1 : Adj y z₁)
    (h2 : Adj z₁ z) : cNorm (D.Ψ z - D.Ψ y) ≤ 4 * δ := by
  have a1 := Ψ_close_adj S W hy h1
  have a2 := Ψ_close_adj S W hz₁ h2
  have e : D.Ψ z - D.Ψ y = (D.Ψ z - D.Ψ z₁) + (D.Ψ z₁ - D.Ψ y) := by
    funext i; simp [Pi.sub_apply, Pi.add_apply]
  rw [e]
  have := cNorm_add_le (D.Ψ z - D.Ψ z₁) (D.Ψ z₁ - D.Ψ y)
  linarith

/-- A block active at a site `z` of layer `m ≥ 2`, whose data is within `4 δ` of that at `y`, has
local solution within `A₂ δ` of that at `y`. -/
theorem active_close (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    {y z : Torus d (N₀ * L ^ k)} (hy : y ∈ G.Ω 1) {m : ℕ} (hm2 : 2 ≤ m) (hmk : m ≤ k)
    (hz : z ∈ G.layer m) (hΨ : cNorm (D.Ψ z - D.Ψ y) ≤ 4 * δ)
    {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ active G z) :
    cNorm (locSol G a ν D.Ψ D.h q.2 - locSol G a ν D.Ψ D.h y) ≤ cA2 d L * δ := by
  have hy1 : y ∈ dataSites G := (mem_dataSites G).2 (Or.inl hy)
  have hδ0 : 0 ≤ δ := (lt_of_le_of_lt (abs_nonneg _) (W.P.r2 y hy1)).le
  obtain ⟨hqi, -⟩ := (mem_active G).1 hq
  obtain ⟨⟨hm1, hmk'⟩, hql, -⟩ := (mem_blockIdx G).1 hqi
  have hq1 : q.2 ∈ dataSites G := (mem_dataSites G).2 (Or.inl (G.layer_subset hm1 hmk' hql))
  obtain ⟨-, f1, -, -⟩ := locSol_facts S W hq1
  obtain ⟨-, f2, -, -⟩ := locSol_facts S W hy1
  have f3 := Ψ_chain S W hm2 hmk hz hq
  have e : locSol G a ν D.Ψ D.h q.2 - locSol G a ν D.Ψ D.h y =
      (locSol G a ν D.Ψ D.h q.2 - D.Ψ q.2) + (D.Ψ q.2 - D.Ψ z) + (D.Ψ z - D.Ψ y) +
        (D.Ψ y - locSol G a ν D.Ψ D.h y) := by
    funext i; simp [Pi.sub_apply, Pi.add_apply]
  rw [e]
  have t1 := cNorm_add_le (locSol G a ν D.Ψ D.h q.2 - D.Ψ q.2) (D.Ψ q.2 - D.Ψ z)
  have t2 := cNorm_add_le (locSol G a ν D.Ψ D.h q.2 - D.Ψ q.2 + (D.Ψ q.2 - D.Ψ z))
    (D.Ψ z - D.Ψ y)
  have t3 := cNorm_add_le (locSol G a ν D.Ψ D.h q.2 - D.Ψ q.2 + (D.Ψ q.2 - D.Ψ z) +
    (D.Ψ z - D.Ψ y)) (D.Ψ y - locSol G a ν D.Ψ D.h y)
  have e2 : cNorm (D.Ψ y - locSol G a ν D.Ψ D.h y) =
      cNorm (locSol G a ν D.Ψ D.h y - D.Ψ y) := vn_sub_comm _ _
  unfold cA2 cA1
  nlinarith

/-- A site of `Ω₁` within distance `2` of a site of layer `n ≥ 3` has layer at least `2`. -/
theorem layer_near2 (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n j : ℕ}
    (hn3 : 3 ≤ n) (hnk : n ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k) {y z : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.layer n) (hz : z ∈ G.layer j)
    (hdist : Green.torusDist d (N₀ * L ^ k) y z ≤ 2) : 2 ≤ j ∧ n ≤ j + 1 ∧ j ≤ n + 1 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hp : (1 : ℝ) ≤ (L : ℝ) ^ j := one_le_pow₀ hL'
  obtain ⟨c1, c2⟩ := layer_bounds_of_dist G hϱ hj1 hjk (by omega) hnk hy hz (by nlinarith) hL
  exact ⟨by omega, c1, c2⟩

end Closeness

section High

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν δ ε : ℝ} {D : BgData G N}

/-- Constants of the mixed second difference at layers `≥ 3`. -/
noncomputable def cMixT1 (d L : ℕ) : ℝ := 9 * 3 ^ d * wH1 d L * ((L : ℝ) + 1) * cA2 d L
noncomputable def cMixHi (d L : ℕ) : ℝ :=
  264 * 3 ^ d * wcM d L * cA2 d L + 650 * cMixT1 d L ^ 2

theorem cMixT1_nonneg (d L : ℕ) : 0 ≤ cMixT1 d L := by
  unfold cMixT1
  have := wH1_nonneg d L
  have : 0 ≤ cA2 d L := by unfold cA2; have := cA1_pos d L; linarith
  positivity

theorem cMixHi_nonneg (d L : ℕ) : 0 ≤ cMixHi d L := by
  unfold cMixHi
  have := wcM_nonneg d L
  have : 0 ≤ cA2 d L := by unfold cA2; have := cA1_pos d L; linarith
  positivity

/-- Blocks active on the unit square at a site of layer `n ≥ 3`, or in the support of the
`τ`-difference at `y + e_μ`, have local solutions within `A₂ δ` of that at `y`. -/
theorem sq_close (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D) {n : ℕ}
    (hn3 : 3 ≤ n) (hnk : n ≤ k) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer n) (μ τ : Fin d) :
    (∀ q ∈ supp4 G y μ τ,
      cNorm (locSol G a ν D.Ψ D.h q.2 - locSol G a ν D.Ψ D.h y) ≤ cA2 d L * δ) ∧
    (∀ q ∈ supp G (y + Pi.single μ 1) τ,
      cNorm (locSol G a ν D.Ψ D.h q.2 - locSol G a ν D.Ψ D.h y) ≤ cA2 d L * δ) := by
  have hL3 := S.hL
  have hL1 : 1 ≤ L := by omega
  have hn2 : 2 ≤ n := by omega
  have hy1 : y ∈ G.Ω 1 := G.layer_subset (by omega) hnk hy
  have hyd : y ∈ dataSites G := (mem_dataSites G).2 (Or.inl hy1)
  have hδ0 : 0 < δ := lt_of_le_of_lt (abs_nonneg _) (W.P.r2 y hyd)
  obtain ⟨n₁, h11, h1k, hy₁, b11, b12⟩ := layer_edge G S.hϱ S.hd hL1 hn3 hnk hy μ
  obtain ⟨n₂, h21, h2k, hy₂, b21, b22⟩ := layer_edge G S.hϱ S.hd hL1 hn3 hnk hy τ
  obtain ⟨n₃, h31, h3k, hy₃, b31, b32⟩ := layer_corner G S.hϱ S.hd hL1 hn3 hnk hy μ τ
  have hy₁Ω : y + Pi.single μ 1 ∈ G.Ω 1 := G.layer_subset (by omega) h1k hy₁
  have z00 : cNorm (D.Ψ y - D.Ψ y) ≤ 4 * δ := by
    rw [sub_self, cNorm_zero']; linarith
  have z10 : cNorm (D.Ψ (y + Pi.single μ 1) - D.Ψ y) ≤ 4 * δ :=
    (Ψ_close_adj S W hy1 (adj_add y μ)).trans (by linarith)
  have z01 : cNorm (D.Ψ (y + Pi.single τ 1) - D.Ψ y) ≤ 4 * δ :=
    (Ψ_close_adj S W hy1 (adj_add y τ)).trans (by linarith)
  have z11 : cNorm (D.Ψ (y + Pi.single μ 1 + Pi.single τ 1) - D.Ψ y) ≤ 4 * δ :=
    Ψ_close_adj2 S W hy1 hy₁Ω (adj_add y μ) (adj_add_add_left y μ τ)
  have c00 := fun q (hq : q ∈ active G y) => active_close S W hy1 hn2 hnk hy z00 hq
  have c10 := fun q (hq : q ∈ active G (y + Pi.single μ 1)) =>
    active_close S W hy1 (by omega) h1k hy₁ z10 hq
  have c01 := fun q (hq : q ∈ active G (y + Pi.single τ 1)) =>
    active_close S W hy1 (by omega) h2k hy₂ z01 hq
  have c11 := fun q (hq : q ∈ active G (y + Pi.single μ 1 + Pi.single τ 1)) =>
    active_close S W hy1 (by omega) h3k hy₃ z11 hq
  refine ⟨?_, ?_⟩
  · intro q hq
    simp only [supp4, Finset.mem_union] at hq
    rcases hq with ((h | h) | h) | h
    · exact c00 q h
    · exact c10 q h
    · exact c01 q h
    · exact c11 q h
  · obtain ⟨m₄, h41, h4k, hy₄⟩ := exists_layer_adj G S.hϱ S.hd hL1 (by omega : 2 ≤ n₁) h1k hy₁
      (adj_sub (y + Pi.single μ 1) τ)
    have hdist4 : Green.torusDist d (N₀ * L ^ k) y
        (y + Pi.single μ 1 - Pi.single τ 1) ≤ 2 := by
      have t1 := (adj_add y μ).torusDist_le
      have t2 := (adj_sub (y + Pi.single μ 1) τ).torusDist_le
      have := Green.torusDist_triangle_gen y (y + Pi.single μ 1)
        (y + Pi.single μ 1 - Pi.single τ 1)
      linarith
    obtain ⟨m42, -, -⟩ := layer_near2 (G := G) S.hϱ S.hd hL1 hn3 hnk h41 h4k hy hy₄ hdist4
    have z4 : cNorm (D.Ψ (y + Pi.single μ 1 - Pi.single τ 1) - D.Ψ y) ≤ 4 * δ :=
      Ψ_close_adj2 S W hy1 hy₁Ω (adj_add y μ) (adj_sub (y + Pi.single μ 1) τ)
    intro q hq
    simp only [supp, Finset.mem_union] at hq
    rcases hq with (h | h) | h
    · exact c10 q h
    · exact c11 q h
    · exact active_close S W hy1 m42 h4k hy₄ z4 h

/-- The first differences from `v₀₀` of the interpolation on the unit square. -/
theorem sq_first (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D) {n : ℕ}
    (hn3 : 3 ≤ n) (hnk : n ≤ k) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer n) (μ τ : Fin d) :
    cNorm (interp G (locSol G a ν D.Ψ D.h) (y + Pi.single μ 1) -
        interp G (locSol G a ν D.Ψ D.h) y) ≤
      9 * 3 ^ d * (wH1 d L * ((L : ℝ) + 1) / (L : ℝ) ^ n * (cA2 d L * δ)) ∧
    cNorm (interp G (locSol G a ν D.Ψ D.h) (y + Pi.single τ 1) -
        interp G (locSol G a ν D.Ψ D.h) y) ≤
      9 * 3 ^ d * (wH1 d L * ((L : ℝ) + 1) / (L : ℝ) ^ n * (cA2 d L * δ)) ∧
    cNorm (interp G (locSol G a ν D.Ψ D.h) (y + Pi.single μ 1 + Pi.single τ 1) -
        interp G (locSol G a ν D.Ψ D.h) y) ≤
      9 * 3 ^ d * (wH1 d L * ((L : ℝ) + 1) / (L : ℝ) ^ n * (cA2 d L * δ)) := by
  have hL3 := S.hL
  have hL1 : 1 ≤ L := by omega
  have hn2 : 2 ≤ n := by omega
  have hy1 : y ∈ G.Ω 1 := G.layer_subset (by omega) hnk hy
  have hyd : y ∈ dataSites G := (mem_dataSites G).2 (Or.inl hy1)
  have hδ0 : 0 < δ := lt_of_le_of_lt (abs_nonneg _) (W.P.r2 y hyd)
  have hA2 : 0 < cA2 d L := by unfold cA2; have := cA1_pos d L; linarith
  have hr0 : 0 ≤ cA2 d L * δ := by positivity
  have hLn : (0 : ℝ) < (L : ℝ) ^ n := by positivity
  obtain ⟨n₁, h11, h1k, hy₁, b11, b12⟩ := layer_edge G S.hϱ S.hd hL1 hn3 hnk hy μ
  obtain ⟨hs4, hs'⟩ := sq_close S W hn3 hnk hy μ τ
  obtain ⟨T10, -, -⟩ := interp_diff G S.hϱ S.hd hL3 (locSol G a ν D.Ψ D.h)
    (locSol G a ν D.Ψ D.h y) hr0 hn2 hnk hy μ
    (fun q hq => locSol_supp_close S W hn3 hnk hy μ hq)
  obtain ⟨T01, -, -⟩ := interp_diff G S.hϱ S.hd hL3 (locSol G a ν D.Ψ D.h)
    (locSol G a ν D.Ψ D.h y) hr0 hn2 hnk hy τ
    (fun q hq => locSol_supp_close S W hn3 hnk hy τ hq)
  obtain ⟨T11, -, -⟩ := interp_diff G S.hϱ S.hd hL3 (locSol G a ν D.Ψ D.h)
    (locSol G a ν D.Ψ D.h y) hr0 (by omega : 2 ≤ n₁) h1k hy₁ τ hs'
  have hH1 := wH1_nonneg d L
  have hpow : (0 : ℝ) ≤ 9 * 3 ^ d := by positivity
  have hT10 : 9 * 3 ^ d * (wH1 d L / (L : ℝ) ^ n * (cA2 d L * δ)) ≤
      9 * 3 ^ d * (wH1 d L * ((L : ℝ) + 1) / (L : ℝ) ^ n * (cA2 d L * δ)) := by
    refine mul_le_mul_of_nonneg_left ?_ hpow
    refine mul_le_mul_of_nonneg_right ?_ hr0
    refine div_le_div_of_nonneg_right ?_ hLn.le
    nlinarith
  refine ⟨T10.trans hT10, T01.trans hT10, ?_⟩
  have hLn1 : (0 : ℝ) < (L : ℝ) ^ n₁ := by positivity
  have hs1 : (L : ℝ) ^ n ≤ L * (L : ℝ) ^ n₁ := scale_ge b11 (by omega)
  have e : interp G (locSol G a ν D.Ψ D.h) (y + Pi.single μ 1 + Pi.single τ 1) -
      interp G (locSol G a ν D.Ψ D.h) y =
      (interp G (locSol G a ν D.Ψ D.h) (y + Pi.single μ 1 + Pi.single τ 1) -
        interp G (locSol G a ν D.Ψ D.h) (y + Pi.single μ 1)) +
      (interp G (locSol G a ν D.Ψ D.h) (y + Pi.single μ 1) -
        interp G (locSol G a ν D.Ψ D.h) y) := by
    funext i; simp [Pi.sub_apply, Pi.add_apply]
  rw [e]
  refine (cNorm_add_le _ _).trans ?_
  have k1 : wH1 d L / (L : ℝ) ^ n₁ ≤ wH1 d L * L / (L : ℝ) ^ n := by
    rw [div_le_div_iff₀ hLn1 hLn]
    nlinarith
  calc _ ≤ 9 * 3 ^ d * (wH1 d L / (L : ℝ) ^ n₁ * (cA2 d L * δ)) +
        9 * 3 ^ d * (wH1 d L / (L : ℝ) ^ n * (cA2 d L * δ)) := add_le_add T11 T10
    _ ≤ 9 * 3 ^ d * (wH1 d L * L / (L : ℝ) ^ n * (cA2 d L * δ)) +
        9 * 3 ^ d * (wH1 d L / (L : ℝ) ^ n * (cA2 d L * δ)) := by gcongr
    _ = _ := by ring

/-- The arithmetic of the final constant. -/
theorem mixHi_arith (d L : ℕ) {δ ℓ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hℓ : 0 < ℓ) :
    22 * (12 * 3 ^ d * (wcM d L / ℓ ^ 2 * (cA2 d L * δ))) +
      650 * (9 * 3 ^ d * (wH1 d L * ((L : ℝ) + 1) / ℓ * (cA2 d L * δ))) ^ 2 ≤
      cMixHi d L * δ / ℓ ^ 2 := by
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have hcm : (0 : ℝ) ≤ cMixT1 d L ^ 2 := sq_nonneg _
  have e : 22 * (12 * 3 ^ d * (wcM d L / ℓ ^ 2 * (cA2 d L * δ))) +
      650 * (9 * 3 ^ d * (wH1 d L * ((L : ℝ) + 1) / ℓ * (cA2 d L * δ))) ^ 2 =
      (264 * 3 ^ d * wcM d L * cA2 d L * δ + 650 * (cMixT1 d L ^ 2 * δ ^ 2)) / ℓ ^ 2 := by
    unfold cMixT1; field_simp; ring
  rw [e]
  unfold cMixHi
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hδ2 hcm]

/-- **Mixed second differences of `φ₀` at layers `≥ 3`.** -/
theorem phi0_sq_high (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    (hs : cA2 d L * δ ≤ 1 / 100) (hδ1 : δ ≤ 1) {n : ℕ} (hn3 : 3 ≤ n) (hnk : n ≤ k)
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer n) (μ τ : Fin d) :
    cNorm (approxField G a ν D.Ψ D.h (y + Pi.single μ 1 + Pi.single τ 1) -
        approxField G a ν D.Ψ D.h (y + Pi.single μ 1) -
        approxField G a ν D.Ψ D.h (y + Pi.single τ 1) + approxField G a ν D.Ψ D.h y) ≤
      cMixHi d L * δ / ((L : ℝ) ^ n) ^ 2 := by
  have hL3 := S.hL
  have hL1 : 1 ≤ L := by omega
  have hn2 : 2 ≤ n := by omega
  have hy1 : y ∈ G.Ω 1 := G.layer_subset (by omega) hnk hy
  have hyd : y ∈ dataSites G := (mem_dataSites G).2 (Or.inl hy1)
  have hδ0 : 0 < δ := lt_of_le_of_lt (abs_nonneg _) (W.P.r2 y hyd)
  have hA2 : 0 < cA2 d L := by unfold cA2; have := cA1_pos d L; linarith
  have hr0 : 0 ≤ cA2 d L * δ := by positivity
  have hLn : (0 : ℝ) < (L : ℝ) ^ n := by positivity
  obtain ⟨n₁, h11, h1k, hy₁, -, -⟩ := layer_edge G S.hϱ S.hd hL1 hn3 hnk hy μ
  obtain ⟨n₂, h21, h2k, hy₂, -, -⟩ := layer_edge G S.hϱ S.hd hL1 hn3 hnk hy τ
  obtain ⟨n₃, h31, h3k, hy₃, -, -⟩ := layer_corner G S.hϱ S.hd hL1 hn3 hnk hy μ τ
  obtain ⟨hs4, -⟩ := sq_close S W hn3 hnk hy μ τ
  obtain ⟨hT10, hT01, hT11⟩ := sq_first S W hn3 hnk hy μ τ
  obtain ⟨hdot, -, -, -⟩ := locSol_facts S W hyd
  have hnorm := locSol_norm_le S W hyd
  rw [phi0_eq_normalize hn2 hnk hy, phi0_eq_normalize (by omega : 2 ≤ n₁) h1k hy₁,
    phi0_eq_normalize (by omega : 2 ≤ n₂) h2k hy₂, phi0_eq_normalize (by omega : 2 ≤ n₃) h3k hy₃]
  have sub4 : ∀ z, (z = y ∨ z = y + Pi.single μ 1 ∨ z = y + Pi.single τ 1 ∨
      z = y + Pi.single μ 1 + Pi.single τ 1) → ∀ q ∈ active G z,
      cNorm (locSol G a ν D.Ψ D.h q.2 - locSol G a ν D.Ψ D.h y) ≤ cA2 d L * δ := by
    intro z hz q hq
    refine hs4 q ?_
    simp only [supp4, Finset.mem_union]
    rcases hz with h | h | h | h <;> subst h
    · exact Or.inl (Or.inl (Or.inl hq))
    · exact Or.inl (Or.inl (Or.inr hq))
    · exact Or.inl (Or.inr hq)
    · exact Or.inr hq
  have i00 := interp_near G (locSol G a ν D.Ψ D.h) (locSol G a ν D.Ψ D.h y) (by omega) hnk hy
    (sub4 y (Or.inl rfl))
  have i10 := interp_near G (locSol G a ν D.Ψ D.h) (locSol G a ν D.Ψ D.h y) (by omega) h1k hy₁
    (sub4 _ (Or.inr (Or.inl rfl)))
  have i01 := interp_near G (locSol G a ν D.Ψ D.h) (locSol G a ν D.Ψ D.h y) (by omega) h2k hy₂
    (sub4 _ (Or.inr (Or.inr (Or.inl rfl))))
  have i11 := interp_near G (locSol G a ν D.Ψ D.h) (locSol G a ν D.Ψ D.h y) (by omega) h3k hy₃
    (sub4 _ (Or.inr (Or.inr (Or.inr rfl))))
  have T2 := interp_sq_le G S.hϱ S.hd hL3 hn3 hnk hy μ τ (locSol G a ν D.Ψ D.h)
    (locSol G a ν D.Ψ D.h y) hr0 hs4
  have key := normalize_mixed hdot hnorm hr0 hs i00 i10 i01 i11 hT10 hT01 hT11 T2
  exact key.trans (mixHi_arith d L hδ0.le hδ1 hLn)

end High

section All

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν δ ε : ℝ} {D : BgData G N}

/-- The constant of the mixed second differences, a function of `(d, L)` only. -/
noncomputable def cMix (d L : ℕ) : ℝ := max (cMixHi d L) (2 * cE d L * (L : ℝ) ^ 4)

theorem cMix_nonneg (d L : ℕ) : 0 ≤ cMix d L := (cMixHi_nonneg d L).trans (le_max_left _ _)

/-- **Mixed second differences of `φ₀` at layers `≥ 2`** (A3, all pairs of directions). -/
theorem phi0_sq (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    (hs : cA2 d L * δ ≤ 1 / 100) (hδ1 : δ ≤ 1) {n : ℕ} (hn2 : 2 ≤ n) (hnk : n ≤ k)
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer n) (μ τ : Fin d) :
    cNorm (approxField G a ν D.Ψ D.h (y + Pi.single μ 1 + Pi.single τ 1) -
        approxField G a ν D.Ψ D.h (y + Pi.single μ 1) -
        approxField G a ν D.Ψ D.h (y + Pi.single τ 1) + approxField G a ν D.Ψ D.h y) ≤
      cMix d L * δ / ((L : ℝ) ^ n) ^ 2 := by
  have hL3 := S.hL
  have hL1 : 1 ≤ L := by omega
  have hy1 : y ∈ G.Ω 1 := G.layer_subset (by omega) hnk hy
  have hyd : y ∈ dataSites G := (mem_dataSites G).2 (Or.inl hy1)
  have hδ0 : 0 < δ := lt_of_le_of_lt (abs_nonneg _) (W.P.r2 y hyd)
  have hLn : (0 : ℝ) < (L : ℝ) ^ n := by positivity
  by_cases hn3 : 3 ≤ n
  · refine (phi0_sq_high S W hs hδ1 hn3 hnk hy μ τ).trans ?_
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le
  · have hn : n = 2 := by omega
    subst hn
    obtain ⟨n₁, h11, h1k, hy₁⟩ := exists_layer_adj G S.hϱ S.hd hL1 hn2 hnk hy (adj_add y μ)
    have hy₁Ω : y + Pi.single μ 1 ∈ G.Ω 1 := G.layer_subset h11 h1k hy₁
    have b1 := phi0_adj_close S W hs hy₁Ω
      (mem_dataSites_of_adj hy₁Ω (adj_add_add_left y μ τ)) (adj_add_add_left y μ τ)
    have b2 := phi0_adj_close S W hs hy1 (mem_dataSites_of_adj hy1 (adj_add y τ)) (adj_add y τ)
    have e : approxField G a ν D.Ψ D.h (y + Pi.single μ 1 + Pi.single τ 1) -
        approxField G a ν D.Ψ D.h (y + Pi.single μ 1) -
        approxField G a ν D.Ψ D.h (y + Pi.single τ 1) + approxField G a ν D.Ψ D.h y =
        (approxField G a ν D.Ψ D.h (y + Pi.single μ 1 + Pi.single τ 1) -
          approxField G a ν D.Ψ D.h (y + Pi.single μ 1)) -
        (approxField G a ν D.Ψ D.h (y + Pi.single τ 1) - approxField G a ν D.Ψ D.h y) := by
      funext i; simp [Pi.sub_apply, Pi.add_apply]; ring
    rw [e]
    refine (cNorm_sub_le _ _).trans ?_
    have hE := cE_pos d L
    have : 2 * (cE d L * δ) ≤ cMix d L * δ / ((L : ℝ) ^ 2) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h4 : ((L : ℝ) ^ 2) ^ 2 = (L : ℝ) ^ 4 := by ring
      rw [h4]
      have h0 : 2 * cE d L * (L : ℝ) ^ 4 ≤ cMix d L := le_max_right _ _
      nlinarith [mul_le_mul_of_nonneg_right h0 hδ0.le]
    linarith

end All

end Balaban.Background
