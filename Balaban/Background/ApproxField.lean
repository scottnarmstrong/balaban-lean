/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ApproxLocal
public import Balaban.Background.Calculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The approximate field: constraint, data and smoothness (LEMMA53-astra.md, §4 (A1)-(A4))

For `δ` with `A₂ δ ≤ 1/100`:

* `phi0_dot`: `φ₀ ⬝ φ₀ = 1` on `Ω₁ ∪ C`;
* `phi0_close_locSol`: `|φ₀ - φ^B| ≤ 12 A₁ δ` (the note's (7));
* `phi0_close_data`: `|φ₀ - Ψ| ≤ C_data δ`;
* `phi0_isSmoothField`: `IsSmoothField G (C_sm δ) φ₀`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Field

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν δ ε : ℝ} {D : BgData G N}

/-- Constants: `B₇ = 12 A₁` for (7), `E = 2 B₇ + 1002` for a crude bond. -/
noncomputable def cB7 (d L : ℕ) : ℝ := 12 * cA1 d L
noncomputable def cE (d L : ℕ) : ℝ := 2 * cB7 d L + 1002

theorem cNorm_zero' : cNorm (0 : Fin N → ℂ) = 0 := by simp [cNorm]

theorem cB7_pos (d L : ℕ) : 0 < cB7 d L := by unfold cB7; have := cA1_pos d L; positivity

theorem cA1_le_cA2 (d L : ℕ) : cA1 d L ≤ cA2 d L := by unfold cA2; linarith

theorem phi0_eq_normalize {x : Torus d (N₀ * L ^ k)} {n : ℕ} (hn2 : 2 ≤ n) (hnk : n ≤ k)
    (hx : x ∈ G.layer n) :
    approxField G a ν D.Ψ D.h x = normalize (interp G (locSol G a ν D.Ψ D.h) x) := by
  classical
  have hx1 : x ∈ G.Ω 1 := G.layer_subset (by omega) hnk hx
  have hl : G.layerIndex x = n := G.layerIndex_eq (by omega) hnk hx
  have : ¬ G.layerIndex x ≤ 1 := by omega
  simp only [approxField, hx1, ite_true, this, ite_false]

theorem phi0_eq_locSol {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G)
    (h : x ∈ G.Ω 1 → G.layerIndex x ≤ 1) :
    approxField G a ν D.Ψ D.h x = locSol G a ν D.Ψ D.h x := by
  classical
  by_cases hx1 : x ∈ G.Ω 1
  · simp only [approxField, hx1, ite_true, h hx1]
  · have hc : x ∈ collar G := ((mem_dataSites G).1 hx).resolve_left hx1
    simp only [approxField, hx1, ite_false, hc, ite_true]

/-- The interpolation is within `A₁ δ` of the local solution at the site. -/
theorem interp_close (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D) {n : ℕ}
    (hn2 : 2 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) :
    cNorm (interp G (locSol G a ν D.Ψ D.h) x - locSol G a ν D.Ψ D.h x) ≤ cA1 d L * δ :=
  interp_near G _ _ (by omega) hnk hx fun q hq => locSol_chain S W hn2 hnk hx hq

theorem phi0_close_locSol (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    (hs : cA2 d L * δ ≤ 1 / 100) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) :
    approxField G a ν D.Ψ D.h y ⬝ᵥ approxField G a ν D.Ψ D.h y = 1 ∧
    cNorm (approxField G a ν D.Ψ D.h y - locSol G a ν D.Ψ D.h y) ≤ cB7 d L * δ := by
  have hδ0 : 0 < δ := lt_of_le_of_lt (abs_nonneg _) (W.P.r2 y hy)
  by_cases hy2 : y ∈ G.Ω 1 ∧ 2 ≤ G.layerIndex y
  · obtain ⟨hy1, hn2⟩ := hy2
    obtain ⟨hm1, hmk, hyl⟩ := G.layerIndex_spec hy1
    rw [phi0_eq_normalize hn2 hmk hyl]
    have hmem : y ∈ dataSites G := hy
    obtain ⟨hdot, -, -, -⟩ := locSol_facts S W hy
    have hnorm := locSol_norm_le S W hy
    have h1 := interp_close S W hn2 hmk hyl
    have hA : cA1 d L * δ ≤ 1 / 100 := (mul_le_mul_of_nonneg_right (cA1_le_cA2 d L) hδ0.le).trans hs
    have := normalize_bounds (ref := locSol G a ν D.Ψ D.h y)
      (v0 := interp G (locSol G a ν D.Ψ D.h) y) (vp := interp G (locSol G a ν D.Ψ D.h) y)
      (vm := interp G (locSol G a ν D.Ψ D.h) y) (a := cA1 d L * δ) (T1 := 0) (T2 := 0)
      hdot hnorm (by have := cA1_pos d L; positivity) hA h1 h1 h1
      (by rw [sub_self, cNorm_zero']) (by rw [sub_self, cNorm_zero'])
      (by
        have : interp G (locSol G a ν D.Ψ D.h) y + interp G (locSol G a ν D.Ψ D.h) y -
            (2 : ℂ) • interp G (locSol G a ν D.Ψ D.h) y = 0 := by
          funext i; simp [Pi.sub_apply, Pi.smul_apply]; ring
        rw [this, cNorm_zero'])
    exact ⟨this.1, by unfold cB7; nlinarith [this.2.1]⟩
  · have hle : y ∈ G.Ω 1 → G.layerIndex y ≤ 1 := fun h => by
      by_contra hc; exact hy2 ⟨h, by omega⟩
    rw [phi0_eq_locSol hy hle]
    obtain ⟨hdot, -, -, -⟩ := locSol_facts S W hy
    refine ⟨hdot, ?_⟩
    rw [sub_self, cNorm_zero']
    have := cB7_pos d L
    positivity


/-- Constants of the smoothness bounds (the note's (6)). -/
noncomputable def cT1 (d L : ℕ) : ℝ := 9 * 3 ^ d * wH1 d L * cA2 d L
noncomputable def cT2 (d L : ℕ) : ℝ := 9 * 3 ^ d * wH2 d L * cA2 d L
noncomputable def cGrad (d L : ℕ) : ℝ := max (cE d L * (L : ℝ) ^ 2) (22 * cT1 d L)
noncomputable def cLapμ (d L : ℕ) : ℝ :=
  max (2 * cE d L * (L : ℝ) ^ 4) (22 * cT2 d L + 440 * cT1 d L ^ 2)
noncomputable def cSm (d L : ℕ) : ℝ := max (cGrad d L) (d * cLapμ d L)

theorem cE_pos (d L : ℕ) : 0 < cE d L := by unfold cE; have := cB7_pos d L; positivity

theorem adj_layers (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hadj : Adj x x') :
    G.layerIndex x ≤ G.layerIndex x' + 1 ∧ G.layerIndex x' ≤ G.layerIndex x + 1 := by
  by_cases hx'1 : x' ∈ G.Ω 1
  · exact ⟨layerIndex_le_succ_of_adj G hϱ hd (by omega) hx hx'1 hadj,
      layerIndex_le_succ_of_adj G hϱ hd (by omega) hx'1 hx hadj.symm⟩
  · have h1 : (1 : ℝ) < ϱ := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have : (2 : ℝ) ≤ L := by exact_mod_cast hL
      nlinarith
    have := layerIndex_eq_one_of_adj_not_mem h1 hL hx hx'1 hadj
    rw [layerIndex_of_not_mem G hx'1]
    omega

theorem phi0_adj_close (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    (hs : cA2 d L * δ ≤ 1 / 100) {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (hx' : x' ∈ dataSites G) (hadj : Adj x x') :
    cNorm (approxField G a ν D.Ψ D.h x' - approxField G a ν D.Ψ D.h x) ≤ cE d L * δ := by
  have hx1 : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
  obtain ⟨-, c1⟩ := phi0_close_locSol S W hs hx1
  obtain ⟨-, c2⟩ := phi0_close_locSol S W hs hx'
  obtain ⟨l1, l2⟩ := adj_layers S.hϱ S.hd S.hL hx hadj
  have c3 := locSol_adj S W hx' hx1 hadj.symm l2 l1
  have e : approxField G a ν D.Ψ D.h x' - approxField G a ν D.Ψ D.h x =
      (approxField G a ν D.Ψ D.h x' - locSol G a ν D.Ψ D.h x') +
      (locSol G a ν D.Ψ D.h x' - locSol G a ν D.Ψ D.h x) +
      (locSol G a ν D.Ψ D.h x - approxField G a ν D.Ψ D.h x) := by
    funext i; simp [Pi.sub_apply, Pi.add_apply]
  rw [e]
  have t1 := cNorm_add_le (approxField G a ν D.Ψ D.h x' - locSol G a ν D.Ψ D.h x')
    (locSol G a ν D.Ψ D.h x' - locSol G a ν D.Ψ D.h x)
  have t2 := cNorm_add_le (approxField G a ν D.Ψ D.h x' - locSol G a ν D.Ψ D.h x' +
    (locSol G a ν D.Ψ D.h x' - locSol G a ν D.Ψ D.h x))
    (locSol G a ν D.Ψ D.h x - approxField G a ν D.Ψ D.h x)
  have e2 : cNorm (locSol G a ν D.Ψ D.h x - approxField G a ν D.Ψ D.h x) =
      cNorm (approxField G a ν D.Ψ D.h x - locSol G a ν D.Ψ D.h x) := vn_sub_comm _ _
  unfold cE
  linarith


theorem mem_dataSites_of_adj {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hadj : Adj x x') :
    x' ∈ dataSites G := by
  by_cases h : x' ∈ G.Ω 1
  · exact (mem_dataSites G).2 (Or.inl h)
  · exact (mem_dataSites G).2 (Or.inr (mem_collar_of_adj G hx h hadj))

/-- Bounds on the bonds at a site of layer `n`: the first differences along `±e_μ` and the centred
second difference. -/
theorem phi0_bond_bounds (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    (hs : cA2 d L * δ ≤ 1 / 100) (hδ1 : δ ≤ 1) {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) (μ : Fin d) :
    cNorm (approxField G a ν D.Ψ D.h (x + Pi.single μ 1) - approxField G a ν D.Ψ D.h x) ≤
        cGrad d L * δ / (L : ℝ) ^ n ∧
    cNorm (approxField G a ν D.Ψ D.h (x - Pi.single μ 1) - approxField G a ν D.Ψ D.h x) ≤
        cGrad d L * δ / (L : ℝ) ^ n ∧
    cNorm (approxField G a ν D.Ψ D.h (x + Pi.single μ 1) +
        approxField G a ν D.Ψ D.h (x - Pi.single μ 1) -
        (2 : ℂ) • approxField G a ν D.Ψ D.h x) ≤ cLapμ d L * δ / ((L : ℝ) ^ n) ^ 2 := by
  have hL3 := S.hL
  have hL1 : 1 ≤ L := by omega
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL3
  have hx1 : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
  have hδ0 : 0 < δ := by
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx1)
    exact lt_of_le_of_lt (abs_nonneg _) (W.P.r2 x hxd)
  have hLn : (0 : ℝ) < (L : ℝ) ^ n := by positivity
  have hE := cE_pos d L
  by_cases hn3 : 3 ≤ n
  · have hn2 : 2 ≤ n := by omega
    have hr0 : 0 ≤ cA2 d L * δ := by
      have : 0 ≤ cA2 d L := by unfold cA2; have := cA1_pos d L; positivity
      positivity
    have hsupp : ∀ q ∈ supp G x μ, cNorm (locSol G a ν D.Ψ D.h q.2 - locSol G a ν D.Ψ D.h x) ≤
        cA2 d L * δ := fun q hq => locSol_supp_close S W hn3 hnk hx μ hq
    obtain ⟨d1, d1', d2⟩ := interp_diff G S.hϱ S.hd hL3 (locSol G a ν D.Ψ D.h)
      (locSol G a ν D.Ψ D.h x) hr0 hn2 hnk hx μ hsupp
    obtain ⟨n₁, h11, h1k, hx₁⟩ := exists_layer_adj G S.hϱ S.hd hL1 hn2 hnk hx (adj_add x μ)
    obtain ⟨n₂, h21, h2k, hx₂⟩ := exists_layer_adj G S.hϱ S.hd hL1 hn2 hnk hx (adj_sub x μ)
    have hx₁1 : x + Pi.single μ 1 ∈ G.Ω 1 := G.layer_subset h11 h1k hx₁
    have hx₂1 : x - Pi.single μ 1 ∈ G.Ω 1 := G.layer_subset h21 h2k hx₂
    have hlx : G.layerIndex x = n := G.layerIndex_eq hn1 hnk hx
    have hn₁ : 2 ≤ n₁ := by
      have := layerIndex_le_succ_of_adj G S.hϱ S.hd hL1 hx1 hx₁1 (adj_add x μ)
      rw [hlx, G.layerIndex_eq h11 h1k hx₁] at this; omega
    have hn₂ : 2 ≤ n₂ := by
      have := layerIndex_le_succ_of_adj G S.hϱ S.hd hL1 hx1 hx₂1 (adj_sub x μ)
      rw [hlx, G.layerIndex_eq h21 h2k hx₂] at this; omega
    rw [phi0_eq_normalize hn2 hnk hx, phi0_eq_normalize hn₁ h1k hx₁, phi0_eq_normalize hn₂ h2k hx₂]
    have a0 := interp_near G (locSol G a ν D.Ψ D.h) (locSol G a ν D.Ψ D.h x) hn1 hnk hx
      (fun q hq => hsupp q (by simp [supp, hq]))
    have ap := interp_near G (locSol G a ν D.Ψ D.h) (locSol G a ν D.Ψ D.h x) h11 h1k hx₁
      (fun q hq => hsupp q (by simp [supp, hq]))
    have am := interp_near G (locSol G a ν D.Ψ D.h) (locSol G a ν D.Ψ D.h x) h21 h2k hx₂
      (fun q hq => hsupp q (by simp [supp, hq]))
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx1)
    obtain ⟨hdot, -, -, -⟩ := locSol_facts S W hxd
    have hnorm := locSol_norm_le S W hxd
    obtain ⟨-, -, N1, N1', N2⟩ := normalize_bounds (ref := locSol G a ν D.Ψ D.h x)
      (v0 := interp G (locSol G a ν D.Ψ D.h) x)
      (vp := interp G (locSol G a ν D.Ψ D.h) (x + Pi.single μ 1))
      (vm := interp G (locSol G a ν D.Ψ D.h) (x - Pi.single μ 1))
      (a := cA2 d L * δ) (T1 := 9 * 3 ^ d * (wH1 d L / (L : ℝ) ^ n * (cA2 d L * δ)))
      (T2 := 9 * 3 ^ d * (wH2 d L / ((L : ℝ) ^ n) ^ 2 * (cA2 d L * δ)))
      hdot hnorm hr0 hs a0 ap am d1 d1' d2
    have hT1 : 22 * (9 * 3 ^ d * (wH1 d L / (L : ℝ) ^ n * (cA2 d L * δ))) =
        22 * cT1 d L * δ / (L : ℝ) ^ n := by unfold cT1; ring
    have hg : 22 * cT1 d L * δ / (L : ℝ) ^ n ≤ cGrad d L * δ / (L : ℝ) ^ n := by
      refine div_le_div_of_nonneg_right ?_ hLn.le
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hδ0.le
    refine ⟨?_, ?_, ?_⟩
    · exact N1.trans (by rw [hT1]; exact hg)
    · exact N1'.trans (by rw [hT1]; exact hg)
    · refine N2.trans ?_
      have hT2 : 22 * (9 * 3 ^ d * (wH2 d L / ((L : ℝ) ^ n) ^ 2 * (cA2 d L * δ))) +
          440 * (9 * 3 ^ d * (wH1 d L / (L : ℝ) ^ n * (cA2 d L * δ))) ^ 2 =
          (22 * cT2 d L * δ + 440 * cT1 d L ^ 2 * δ ^ 2) / ((L : ℝ) ^ n) ^ 2 := by
        unfold cT1 cT2; field_simp
      rw [hT2]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have h0 : 22 * cT2 d L + 440 * cT1 d L ^ 2 ≤ cLapμ d L := le_max_right _ _
      have h1 : δ ^ 2 ≤ δ := by nlinarith
      have h2 : 0 ≤ 440 * cT1 d L ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h0 hδ0.le]
  · -- crude bound
    have hn : n ≤ 2 := by omega
    have hLn2 : (L : ℝ) ^ n ≤ (L : ℝ) ^ 2 := pow_le_pow_right₀ (by linarith) hn
    have b1 := phi0_adj_close S W hs hx1 (mem_dataSites_of_adj hx1 (adj_add x μ)) (adj_add x μ)
    have b2 := phi0_adj_close S W hs hx1 (mem_dataSites_of_adj hx1 (adj_sub x μ)) (adj_sub x μ)
    have hg : cE d L * δ ≤ cGrad d L * δ / (L : ℝ) ^ n := by
      rw [le_div_iff₀ hLn]
      have h0 : cE d L * (L : ℝ) ^ 2 ≤ cGrad d L := le_max_left _ _
      have h1 : cE d L * δ * (L : ℝ) ^ n ≤ cE d L * δ * (L : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hLn2 (by positivity)
      have h2 : cE d L * (L : ℝ) ^ 2 * δ ≤ cGrad d L * δ := mul_le_mul_of_nonneg_right h0 hδ0.le
      linarith
    refine ⟨b1.trans hg, b2.trans hg, ?_⟩
    have e : approxField G a ν D.Ψ D.h (x + Pi.single μ 1) +
        approxField G a ν D.Ψ D.h (x - Pi.single μ 1) - (2 : ℂ) • approxField G a ν D.Ψ D.h x =
        (approxField G a ν D.Ψ D.h (x + Pi.single μ 1) - approxField G a ν D.Ψ D.h x) +
        (approxField G a ν D.Ψ D.h (x - Pi.single μ 1) - approxField G a ν D.Ψ D.h x) := by
      funext i; simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]; ring
    rw [e]
    refine (cNorm_add_le _ _).trans ?_
    have : 2 * (cE d L * δ) ≤ cLapμ d L * δ / ((L : ℝ) ^ n) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h4 : ((L : ℝ) ^ n) ^ 2 ≤ (L : ℝ) ^ 4 := by
        calc ((L : ℝ) ^ n) ^ 2 ≤ ((L : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hLn.le hLn2 2
          _ = (L : ℝ) ^ 4 := by ring
      have h0 : 2 * cE d L * (L : ℝ) ^ 4 ≤ cLapμ d L := le_max_left _ _
      have h1 : 2 * (cE d L * δ) * ((L : ℝ) ^ n) ^ 2 ≤ 2 * (cE d L * δ) * (L : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      have h2 : 2 * cE d L * (L : ℝ) ^ 4 * δ ≤ cLapμ d L * δ := mul_le_mul_of_nonneg_right h0 hδ0.le
      linarith
    linarith


/-- **(A3)**: the approximate field is smooth at the scale of each site. -/
theorem phi0_isSmoothField (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    (hs : cA2 d L * δ ≤ 1 / 100) (hδ1 : δ ≤ 1) :
    IsSmoothField G (cSm d L * δ) (approxField G a ν D.Ψ D.h) := by
  have hL3 := S.hL
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL3
  refine ⟨fun x hx μ => ?_, fun x hx => ?_⟩
  · obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
    obtain ⟨b1, b2, -⟩ := phi0_bond_bounds S W hs hδ1 hn1 hnk hxl μ
    have hδ0 : 0 < δ := by
      have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
      exact lt_of_le_of_lt (abs_nonneg _) (W.P.r2 x hxd)
    have hLn : (0 : ℝ) < (L : ℝ) ^ G.layerIndex x := by positivity
    have hc : cGrad d L * δ / (L : ℝ) ^ G.layerIndex x ≤
        cSm d L * δ / G.spacing x := by
      unfold GeneratingSet.spacing
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le) hLn.le
    exact ⟨b1.trans hc, b2.trans hc⟩
  · obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
    have hδ0 : 0 < δ := by
      have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
      exact lt_of_le_of_lt (abs_nonneg _) (W.P.r2 x hxd)
    set n := G.layerIndex x with hn
    have e : (fun i => ∑ μ : Fin d, (approxField G a ν D.Ψ D.h (x + Pi.single μ 1) i +
        approxField G a ν D.Ψ D.h (x - Pi.single μ 1) i - 2 * approxField G a ν D.Ψ D.h x i)) =
        ∑ μ : Fin d, (approxField G a ν D.Ψ D.h (x + Pi.single μ 1) +
          approxField G a ν D.Ψ D.h (x - Pi.single μ 1) -
          (2 : ℂ) • approxField G a ν D.Ψ D.h x) := by
      funext i
      simp [Finset.sum_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    show cNorm _ ≤ _
    rw [e]
    refine (cNorm_sum_le _ _).trans ?_
    have hb : ∀ μ : Fin d, cNorm (approxField G a ν D.Ψ D.h (x + Pi.single μ 1) +
          approxField G a ν D.Ψ D.h (x - Pi.single μ 1) -
          (2 : ℂ) • approxField G a ν D.Ψ D.h x) ≤ cLapμ d L * δ / ((L : ℝ) ^ n) ^ 2 :=
      fun μ => (phi0_bond_bounds S W hs hδ1 hn1 hnk hxl μ).2.2
    calc _ ≤ ∑ _μ : Fin d, cLapμ d L * δ / ((L : ℝ) ^ n) ^ 2 := Finset.sum_le_sum fun μ _ => hb μ
      _ = d * (cLapμ d L * δ / ((L : ℝ) ^ n) ^ 2) := by simp
      _ ≤ cSm d L * δ / G.spacing x ^ 2 := by
        unfold GeneratingSet.spacing
        rw [← hn, ← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
        have : (d : ℝ) * cLapμ d L ≤ cSm d L := le_max_right _ _
        nlinarith

end Field

end Balaban.Background
