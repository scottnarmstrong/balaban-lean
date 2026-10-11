/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ApproxField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The residual of the approximate field (LEMMA53-astra.md, §4 (A5), (10))

`residual G a ν D φ = S(Ψ, h̃) - H_D(0) φ|_{Ω₁}` and its exact formula (10):
`f₀(x) = a_n L^{-2n} (Ψ(x) - Q_n φ(x)) + ν (h̃(x) - φ(x)) + Δφ̄(x) + ∑_{z ∈ C, z ∼ x} (Ψ(z) - φ(z))`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Residual

variable (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ)

/-- **The residual** `f₀ = S(Ψ, h̃) - H_D(0) φ₀` of a field `φ` (the multiplier `α₀ = 0`). -/
noncomputable def residual (D : BgData G N) (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    G.Ω 1 × Fin N → ℂ :=
  source G a ν D - liftOp N (dirichletOperator G a ν (0 : G.Ω 1 → ℂ)) *ᵥ (fun p => φ p.1 p.2)

variable {G a ν}

theorem zeroExt_add_collar_field (D : BgData G N) (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (i : Fin N)
    {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hxy : Adj x y) :
    zeroExt (G.Ω 1) (fun z : G.Ω 1 => φ z.1 i) y +
      (if y ∈ collar G then D.Ψ y i else 0) =
    φ y i + (if y ∈ collar G then D.Ψ y i - φ y i else 0) := by
  classical
  by_cases hy : y ∈ G.Ω 1
  · have hc : y ∉ collar G := fun h => ((mem_collar G).1 h).1 hy
    simp [zeroExt, hy, hc]
  · have hc : y ∈ collar G := mem_collar_of_adj G hx hy hxy
    simp [zeroExt, hy, hc]

theorem residual_apply (D : BgData G N) (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (x : G.Ω 1) (i : Fin N) :
    residual G a ν D φ (x, i) =
      ((a (G.layerIndex x.1) / ((L : ℝ) ^ G.layerIndex x.1) ^ 2 : ℝ) : ℂ) *
        (D.Ψ x.1 i - ((((((L : ℝ) ^ G.layerIndex x.1) ^ d)⁻¹ : ℝ)) : ℂ) *
          ∑ y ∈ G.blk (G.layerIndex x.1) x.1, φ y i) +
      (ν : ℂ) * (D.h x.1 i - φ x.1 i) +
      ∑ μ : Fin d, (φ (x.1 + Pi.single μ 1) i + φ (x.1 - Pi.single μ 1) i - 2 * φ x.1 i) +
      ∑ μ : Fin d, ((if x.1 + Pi.single μ 1 ∈ collar G then
          D.Ψ (x.1 + Pi.single μ 1) i - φ (x.1 + Pi.single μ 1) i else 0) +
        (if x.1 - Pi.single μ 1 ∈ collar G then
          D.Ψ (x.1 - Pi.single μ 1) i - φ (x.1 - Pi.single μ 1) i else 0)) := by
  classical
  have hx := x.2
  obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
  unfold residual
  simp only [Pi.sub_apply]
  rw [liftOp_mulVec, dirichlet_apply]
  simp only [source, qStar, boundaryTerm, negLap, blockTerm, Pi.zero_apply, zero_mul, add_zero]
  have hblk : ∑ y ∈ G.blk (G.layerIndex x.1) x.1, zeroExt (G.Ω 1) (fun z : G.Ω 1 => φ z.1 i) y =
      ∑ y ∈ G.blk (G.layerIndex x.1) x.1, φ y i := by
    refine Finset.sum_congr rfl fun y hy => ?_
    have hyΩ : y ∈ G.Ω 1 := G.layer_subset hn1 hnk (mem_layer_of_mem_blk G hn1 hnk hxl hy)
    exact zeroExt_mem (G.Ω 1) (fun z : G.Ω 1 => φ z.1 i) ⟨y, hyΩ⟩
  rw [hblk]
  have hxx : zeroExt (G.Ω 1) (fun z : G.Ω 1 => φ z.1 i) x.1 = φ x.1 i :=
    zeroExt_mem (G.Ω 1) (fun z : G.Ω 1 => φ z.1 i) x
  have key : ∀ μ : Fin d,
      ((if x.1 + Pi.single μ 1 ∈ collar G then D.Ψ (x.1 + Pi.single μ 1) i else 0) +
        (if x.1 - Pi.single μ 1 ∈ collar G then D.Ψ (x.1 - Pi.single μ 1) i else 0)) -
        (2 * φ x.1 i - zeroExt (G.Ω 1) (fun z : G.Ω 1 => φ z.1 i) (x.1 + Pi.single μ 1) -
          zeroExt (G.Ω 1) (fun z : G.Ω 1 => φ z.1 i) (x.1 - Pi.single μ 1)) =
      (φ (x.1 + Pi.single μ 1) i + φ (x.1 - Pi.single μ 1) i - 2 * φ x.1 i) +
      ((if x.1 + Pi.single μ 1 ∈ collar G then
          D.Ψ (x.1 + Pi.single μ 1) i - φ (x.1 + Pi.single μ 1) i else 0) +
        (if x.1 - Pi.single μ 1 ∈ collar G then
          D.Ψ (x.1 - Pi.single μ 1) i - φ (x.1 - Pi.single μ 1) i else 0)) := by
    intro μ
    have h1 := zeroExt_add_collar_field D φ i hx (adj_add x.1 μ)
    have h2 := zeroExt_add_collar_field D φ i hx (adj_sub x.1 μ)
    linear_combination h1 + h2
  have hsum := Finset.sum_congr (rfl : (univ : Finset (Fin d)) = univ) fun μ _ => key μ
  rw [hxx]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum ⊢
  linear_combination hsum

end Residual

section ResidualBound

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν δ ε : ℝ} {D : BgData G N}

/-- Within a block of layer `n`, the local solution is constant. -/
theorem locSol_blk {n : ℕ} {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) (hn1 : 1 ≤ n)
    (hnk : n ≤ k) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.blk n x) {a : ℕ → ℝ} {ν : ℝ} (D : BgData G N) :
    locSol G a ν D.Ψ D.h y = locSol G a ν D.Ψ D.h x := by
  classical
  have hyl : y ∈ G.layer n := mem_layer_of_mem_blk G hn1 hnk hx hy
  have hy1 : y ∈ G.Ω 1 := G.layer_subset hn1 hnk hyl
  have hx1 : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
  have hly : G.layerIndex y = n := G.layerIndex_eq hn1 hnk hyl
  have hlx : G.layerIndex x = n := G.layerIndex_eq hn1 hnk hx
  have hΨ := D.Ψ_layerConst n hn1 hnk x hx y hy
  have hh := D.h_layerConst n hn1 hnk x hx y hy
  simp only [locSol, hy1, hx1, ite_true, hly, hlx, blockMass, hΨ, hh]

theorem Qv_close (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    (hs : cA2 d L * δ ≤ 1 / 100) {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) :
    cNorm (locSol G a ν D.Ψ D.h x - ((((((L : ℝ) ^ n) ^ d)⁻¹ : ℝ)) : ℂ) •
      ∑ y ∈ G.blk n x, approxField G a ν D.Ψ D.h y) ≤ cB7 d L * δ := by
  have hcard := card_blk_cast G n hnk x
  have hp : (0 : ℝ) < ((L : ℝ) ^ n) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hδ0 : 0 ≤ δ := by
    have hxd : x ∈ dataSites G :=
      (mem_dataSites G).2 (Or.inl (G.layer_subset hn1 hnk hx))
    exact (lt_of_le_of_lt (abs_nonneg _) (W.P.r2 x hxd)).le
  have e : locSol G a ν D.Ψ D.h x - ((((((L : ℝ) ^ n) ^ d)⁻¹ : ℝ)) : ℂ) •
      ∑ y ∈ G.blk n x, approxField G a ν D.Ψ D.h y =
      ((((((L : ℝ) ^ n) ^ d)⁻¹ : ℝ)) : ℂ) •
        ∑ y ∈ G.blk n x, (locSol G a ν D.Ψ D.h x - approxField G a ν D.Ψ D.h y) := by
    have hc : (((((L : ℝ) ^ n) ^ d)⁻¹ : ℝ) : ℂ) * ((G.blk n x).card : ℂ) = 1 := by
      have : (((((L : ℝ) ^ n) ^ d)⁻¹ : ℝ)) * ((G.blk n x).card : ℝ) = 1 := by
        rw [hcard]; exact inv_mul_cancel₀ hp.ne'
      exact_mod_cast this
    have hc1 : (((((L : ℝ) ^ n) ^ d)⁻¹ : ℝ) : ℂ) • ((G.blk n x).card • locSol G a ν D.Ψ D.h x) =
        locSol G a ν D.Ψ D.h x := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc, one_smul]
    rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub, hc1]
  rw [e, cNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp)]
  refine (mul_le_mul_of_nonneg_left (cNorm_sum_le _ _) (inv_pos.2 hp).le).trans ?_
  calc (((L : ℝ) ^ n) ^ d)⁻¹ * ∑ y ∈ G.blk n x,
        cNorm (locSol G a ν D.Ψ D.h x - approxField G a ν D.Ψ D.h y)
      ≤ (((L : ℝ) ^ n) ^ d)⁻¹ * ∑ _y ∈ G.blk n x, cB7 d L * δ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y hy => ?_) (inv_pos.2 hp).le
        have hyl : y ∈ G.layer n := mem_layer_of_mem_blk G hn1 hnk hx hy
        have hyd : y ∈ dataSites G :=
          (mem_dataSites G).2 (Or.inl (G.layer_subset hn1 hnk hyl))
        obtain ⟨-, c⟩ := phi0_close_locSol S W hs hyd
        rw [← locSol_blk hx hn1 hnk hy D]
        have := vn_sub_comm (locSol G a ν D.Ψ D.h y) (approxField G a ν D.Ψ D.h y)
        have e2 : cNorm (locSol G a ν D.Ψ D.h y - approxField G a ν D.Ψ D.h y) =
            cNorm (approxField G a ν D.Ψ D.h y - locSol G a ν D.Ψ D.h y) := this
        rw [e2]; exact c
    _ = cB7 d L * δ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        field_simp


noncomputable def cRes (d L : ℕ) : ℝ := 3 * cB7 d L + 256 + cSm d L + 1000 * d * (L : ℝ) ^ 2

/-- **(A5)**: the residual is `O(δ)` at the scale of each site. -/
theorem residual_bound (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    (hs : cA2 d L * δ ≤ 1 / 100) (hδ1 : δ ≤ 1) (x : G.Ω 1) :
    G.spacing x.1 ^ 2 * cNorm (fun i => residual G a ν D (approxField G a ν D.Ψ D.h) (x, i)) ≤
      cRes d L * δ := by
  classical
  have hx := x.2
  obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
  have hL3 := S.hL
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL3
  have hxd : x.1 ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
  have hδ0 : 0 < δ := lt_of_le_of_lt (abs_nonneg _) (W.P.r2 x.1 hxd)
  obtain ⟨hdot, hnear, hre, hmult⟩ := locSol_facts S W hxd
  have hnorm := locSol_norm_le S W hxd
  have hmult := hmult hx
  obtain ⟨hB0, hB1⟩ := blockMass_le S hx
  have ham := S.ha _ hn1 hnk
  have hΦ : locSol G a ν D.Ψ D.h x.1 =
      cMinimizer (a (G.layerIndex x.1)) (blockMass G ν x.1) (D.Ψ x.1) (D.h x.1) := by
    simp only [locSol, hx, ite_true]
  have hre' : (1 / 8 : ℝ) ≤ (cBlend (a (G.layerIndex x.1)) (blockMass G ν x.1) (D.Ψ x.1) (D.h x.1) ⬝ᵥ
      cBlend (a (G.layerIndex x.1)) (blockMass G ν x.1) (D.Ψ x.1) (D.h x.1)).re := by
    simpa [hx] using hre
  have hne : cBlend (a (G.layerIndex x.1)) (blockMass G ν x.1) (D.Ψ x.1) (D.h x.1) ⬝ᵥ
      cBlend (a (G.layerIndex x.1)) (blockMass G ν x.1) (D.Ψ x.1) (D.h x.1) ≠ 0 := by
    intro h0; rw [h0] at hre'; simp at hre'; linarith
  have hCEL := cMinimizer_isCEL hne
  rw [← hΦ] at hCEL
  generalize hn : G.layerIndex x.1 = n at *
  have hℓ : (0 : ℝ) < (L : ℝ) ^ n := by
    have : (0 : ℝ) < L := by linarith
    positivity
  have hℓC : (((L : ℝ) ^ n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hspacing : G.spacing x.1 = (L : ℝ) ^ n := by rw [GeneratingSet.spacing, hn]
  have hbm : blockMass G ν x.1 = ν * ((L : ℝ) ^ n) ^ 2 := by unfold blockMass; rw [hn]
  set α := cMultiplier (a n) (blockMass G ν x.1) (D.Ψ x.1) (D.h x.1) with hα
  set Φ := locSol G a ν D.Ψ D.h x.1 with hΦdef
  set φ := approxField G a ν D.Ψ D.h with hφ
  set Qv : Fin N → ℂ := ((((((L : ℝ) ^ n) ^ d)⁻¹ : ℝ)) : ℂ) • ∑ y ∈ G.blk n x.1, φ y with hQv
  set V3 : Fin N → ℂ := fun i => ∑ μ : Fin d,
    (φ (x.1 + Pi.single μ 1) i + φ (x.1 - Pi.single μ 1) i - 2 * φ x.1 i) with hV3
  set V4 : Fin N → ℂ := ∑ μ : Fin d, ((if x.1 + Pi.single μ 1 ∈ collar G then
      D.Ψ (x.1 + Pi.single μ 1) - φ (x.1 + Pi.single μ 1) else 0) +
    (if x.1 - Pi.single μ 1 ∈ collar G then
      D.Ψ (x.1 - Pi.single μ 1) - φ (x.1 - Pi.single μ 1) else 0)) with hV4
  have hR : ((((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) • (fun i => residual G a ν D φ (x, i)) =
      α • Φ + (a n : ℂ) • (Φ - Qv) + (blockMass G ν x.1 : ℂ) • (Φ - φ x.1) +
        ((((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) • V3 + ((((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) • V4 := by
    funext i
    have hi := congrFun (show (a n : ℂ) • (Φ - D.Ψ x.1) + (blockMass G ν x.1 : ℂ) • (Φ - D.h x.1) + α • Φ = 0 from hCEL) i
    simp only [ Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at hi
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [residual_apply, hQv, hV3, hV4, hn]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.add_apply]
    rw [hbm]
    rw [hbm] at hi
    have hite : ∀ (P : Prop) [Decidable P] (u : Fin N → ℂ), (if P then u else 0) i =
        if P then u i else 0 := fun P _ u => by split_ifs <;> simp
    simp only [hite, Pi.sub_apply]
    push_cast at hi hℓC ⊢
    generalize (L : ℂ) ^ n = ℓc at *
    field_simp
    linear_combination (-(ℓc ^ d)) * hi
  have hϱ1 : (1 : ℝ) < ϱ := by
    have h1 : (1 : ℝ) ≤ d := by exact_mod_cast S.hd
    have := S.hϱ
    nlinarith
  -- the collar terms
  have hcol : ∀ z, Adj x.1 z → ((L : ℝ) ^ n) ^ 2 *
      cNorm (if z ∈ collar G then D.Ψ z - φ z else 0) ≤ 500 * (L : ℝ) ^ 2 * δ := by
    intro z hadj
    by_cases hz : z ∈ collar G
    · have hzΩ : z ∉ G.Ω 1 := ((mem_collar G).1 hz).1
      have hl1 : G.layerIndex x.1 = 1 := layerIndex_eq_one_of_adj_not_mem hϱ1 hL3 hx hzΩ hadj
      have hn1' : n = 1 := by rw [← hn]; exact hl1
      have hzd : z ∈ dataSites G := (mem_dataSites G).2 (Or.inr hz)
      have hφz : φ z = locSol G a ν D.Ψ D.h z :=
        phi0_eq_locSol hzd (fun h => absurd h hzΩ)
      obtain ⟨-, hz2, -, -⟩ := locSol_facts S W hzd
      simp only [hz, ite_true]
      rw [hφz, hn1']
      have e : cNorm (D.Ψ z - locSol G a ν D.Ψ D.h z) = cNorm (locSol G a ν D.Ψ D.h z - D.Ψ z) :=
        vn_sub_comm _ _
      rw [e]
      have : ((L : ℝ) ^ 1) ^ 2 * cNorm (locSol G a ν D.Ψ D.h z - D.Ψ z) ≤
          ((L : ℝ) ^ 1) ^ 2 * (500 * δ) := mul_le_mul_of_nonneg_left hz2 (by positivity)
      nlinarith
    · simp only [hz, ite_false, cNorm_zero', mul_zero]
      positivity
  have hLHS : cNorm (((((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) • (fun i => residual G a ν D φ (x, i))) =
      ((L : ℝ) ^ n) ^ 2 * cNorm (fun i => residual G a ν D φ (x, i)) := by
    rw [cNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hspacing, ← hLHS, hR]
  -- bounds of the five pieces
  have b1 : cNorm (α • Φ) ≤ 256 * δ := by
    rw [cNorm_smul]; nlinarith [norm_nonneg α, cNorm_nonneg Φ]
  have bQ := Qv_close S W hs hn1 hnk hxl
  have b2 : cNorm ((a n : ℂ) • (Φ - Qv)) ≤ 2 * (cB7 d L * δ) := by
    rw [cNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ham.1])]
    exact mul_le_mul ham.2 bQ (cNorm_nonneg _) (by norm_num)
  have b3 : cNorm ((blockMass G ν x.1 : ℂ) • (Φ - φ x.1)) ≤ 1 * (cB7 d L * δ) := by
    rw [cNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB0]
    obtain ⟨-, c⟩ := phi0_close_locSol S W hs hxd
    have e : cNorm (Φ - φ x.1) = cNorm (φ x.1 - Φ) := vn_sub_comm _ _
    rw [e]
    exact mul_le_mul hB1 c (cNorm_nonneg _) zero_le_one
  have b4 : cNorm (((((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) • V3) ≤ cSm d L * δ := by
    have hsm := (phi0_isSmoothField S W hs hδ1).lap x.1 hx
    rw [hspacing] at hsm
    rw [cNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : cNorm V3 ≤ cSm d L * δ / ((L : ℝ) ^ n) ^ 2 := hsm
    calc ((L : ℝ) ^ n) ^ 2 * cNorm V3 ≤ ((L : ℝ) ^ n) ^ 2 * (cSm d L * δ / ((L : ℝ) ^ n) ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = cSm d L * δ := by field_simp
  have b5 : cNorm (((((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) • V4) ≤ 1000 * d * (L : ℝ) ^ 2 * δ := by
    rw [cNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hV4le : cNorm V4 ≤ ∑ μ : Fin d, (cNorm (if x.1 + Pi.single μ 1 ∈ collar G then
        D.Ψ (x.1 + Pi.single μ 1) - φ (x.1 + Pi.single μ 1) else 0) +
        cNorm (if x.1 - Pi.single μ 1 ∈ collar G then
        D.Ψ (x.1 - Pi.single μ 1) - φ (x.1 - Pi.single μ 1) else 0)) := by
      refine (cNorm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => cNorm_add_le _ _)
    calc ((L : ℝ) ^ n) ^ 2 * cNorm V4 ≤ ((L : ℝ) ^ n) ^ 2 * ∑ μ : Fin d,
          (cNorm (if x.1 + Pi.single μ 1 ∈ collar G then
            D.Ψ (x.1 + Pi.single μ 1) - φ (x.1 + Pi.single μ 1) else 0) +
          cNorm (if x.1 - Pi.single μ 1 ∈ collar G then
            D.Ψ (x.1 - Pi.single μ 1) - φ (x.1 - Pi.single μ 1) else 0)) :=
          mul_le_mul_of_nonneg_left hV4le (by positivity)
      _ = ∑ μ : Fin d, (((L : ℝ) ^ n) ^ 2 * cNorm (if x.1 + Pi.single μ 1 ∈ collar G then
            D.Ψ (x.1 + Pi.single μ 1) - φ (x.1 + Pi.single μ 1) else 0) +
          ((L : ℝ) ^ n) ^ 2 * cNorm (if x.1 - Pi.single μ 1 ∈ collar G then
            D.Ψ (x.1 - Pi.single μ 1) - φ (x.1 - Pi.single μ 1) else 0)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun μ _ => by ring
      _ ≤ ∑ _μ : Fin d, (500 * (L : ℝ) ^ 2 * δ + 500 * (L : ℝ) ^ 2 * δ) :=
          Finset.sum_le_sum fun μ _ =>
            add_le_add (hcol _ (adj_add x.1 μ)) (hcol _ (adj_sub x.1 μ))
      _ = 1000 * d * (L : ℝ) ^ 2 * δ := by simp; ring
  have t1 := cNorm_add_le (α • Φ + (a n : ℂ) • (Φ - Qv) + (blockMass G ν x.1 : ℂ) • (Φ - φ x.1) +
    ((((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) • V3) (((((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) • V4)
  have t2 := cNorm_add_le (α • Φ + (a n : ℂ) • (Φ - Qv) + (blockMass G ν x.1 : ℂ) • (Φ - φ x.1))
    (((((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) • V3)
  have t3 := cNorm_add_le (α • Φ + (a n : ℂ) • (Φ - Qv)) ((blockMass G ν x.1 : ℂ) • (Φ - φ x.1))
  have t4 := cNorm_add_le (α • Φ) ((a n : ℂ) • (Φ - Qv))
  unfold cRes
  nlinarith

end ResidualBound

end Balaban.Background
