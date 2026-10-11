/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.GoldstoneStep

/-!
# Root-C from Root-F, C-1* and the Gaussian kernel hypotheses (CORRELATIONS.md Theorem 3.1)

`rootC_of_rootF_c1Star`: if the clauses of Root-F at `κ = κ_*`, `c₉ = 1` and the interface C-1*
hold for the same integers `L, M` (`RootFAndC1Star`), and the Gaussian kernel hypotheses
(`KernelHyp`, and `KernelHypLarge` at the masses `μ ∈ (0, 2]`) hold for the constant `a` of C-1*,
then `RootCStatement d N` holds.  Steps A–E of CORRELATIONS.md §3:

* A: `exists_limits`, `bullet_one` (`LimAlong.lean`), from the clauses of Root-F;
* B: `bounds_pos_nu` (`BoundsNu.lean`);
* C: `tendsto_mag`, `tendsto_mainSum` (`ZeroLimit.lean`);
* D, E: `limits_zero` (`GoldstoneStep.lean`): the lattice Green's function and the Goldstone
  asymptotics.
-/

@[expose] public section

open Filter Topology Finset

namespace Balaban.Correlations

open Balaban Balaban.Flow

theorem norm_single_idx {N : ℕ} (hN : 2 ≤ N) :
    ‖(EuclideanSpace.single (idx₀ hN) (1 : ℝ) : EuclideanSpace ℝ (Fin N))‖ = 1 := by
  simp

/-- **Theorem 3.1** (CORRELATIONS.md): Root-C from Root-F, C-1* and the kernel hypotheses. -/
theorem rootC_of_rootF_c1Star (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N)
    (hjoint : RootFAndC1Star d N hN)
    (hG : ∀ (L : ℕ) [NeZero L] (a : ℝ), 3 ≤ L → 1 / (2 * (1 - ((L : ℝ) ^ 2)⁻¹)) < a → a < 3 / 2 →
      ∃ (t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
        (t0 : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (C_G δ_G C_P : ℝ),
        KernelHyp d L a t t0 C_G δ_G C_P ∧ KernelHypLarge d L a t C_G δ_G) :
    RootCStatement d N := by
  intro _ _
  obtain ⟨δ, hδ, L, M, hL3, hM, β₀F, hF, ⟨C⟩⟩ := hjoint
  have hL : 2 ≤ L := by omega
  have : NeZero L := ⟨by omega⟩
  rcases C with ⟨a, γ₀, cS, cX, cP, ρ₀, ρ₁, βS, J, ha_r, hγr, hcS, hcX, hcP, hρ₀r, hρ₁r,
    hJp, hJt, hJb, data⟩
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have ha : 0 < a := by
    refine lt_trans ?_ ha_r.1
    have : ((L : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hL1 (by norm_num))
    have : 0 < 1 - ((L : ℝ) ^ 2)⁻¹ := by linarith
    positivity
  obtain ⟨t, t0, C_G, δ_G, C_P, H, HL⟩ := hG L a hL3 ha_r.1 ha_r.2
  have hCG := H.nonneg_G
  obtain ⟨C1, hC1nn, hC1⟩ := exists_abs_mainSum_le hd hL H.pos_δ hCG
  obtain ⟨C2, hC2nn, hC2⟩ := goldstone_uniform hL1 d hd hγr.1 H.pos_δ
  set q : ℝ := rate (L : ℝ) γ₀ with hq
  have hq0 : 0 ≤ q := (rate_pos hL0 γ₀).le
  have hq1 : q < 1 := rate_lt_one hL1 hγr.1
  have h1q : 0 < 1 - q := by linarith
  set K : ℝ := K1 L cS ρ₀ with hK
  have hK0 : 0 ≤ K := K1_nonneg hL hcS.le hρ₀r.1
  set A3 : ℝ := cX * q / (2 * (1 - q)) with hA3
  have hA30 : 0 ≤ A3 := by positivity
  set c : ℝ := cS + K + 1 + ((1 + K) ^ 2 * (2 * C_G * C1) +
    (1 + K) ^ 2 * (Real.exp 2 * A3 * C_G * C2)) + A3 with hc
  have hW1 : 0 ≤ (1 + K) ^ 2 * (2 * C_G * C1) := by positivity
  have hW2 : 0 ≤ (1 + K) ^ 2 * (Real.exp 2 * A3 * C_G * C2) := by positivity
  set c' : ℝ := min cP (δ_G / (2 * (L : ℝ) ^ 2)) with hc'
  have hρC : 0 < min ρ₀ (2 * γ₀) := lt_min hρ₀r.1 (by linarith [hγr.1])
  refine ⟨max (max β₀F βS) (max 1 (2 * cX * q / (1 - q))), c, c', min ρ₀ (2 * γ₀), ρ₁, M * L,
    by nlinarith, by linarith, lt_min hcP (by have := H.pos_δ; positivity), hρC, hρ₁r.1, hρ₁r.2,
    ?_⟩
  intro β hβ
  have hβF : β₀F ≤ β := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hβ
  have hβS : βS ≤ β := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hβ
  have hβ1 : 1 ≤ β := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hβ
  have hβ2 : 2 * cX * q / (1 - q) ≤ β :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hβ
  have hβpos : 0 < β := by linarith
  obtain ⟨ξ, μ, rtr, rlg, em, rtrLim, rlgLim, rtrZero, rlgZero, h1, h2, h3⟩ := data β hβS
  have HS : ∀ ν ∈ Set.Icc (0 : ℝ) 1, SeqHyp L γ₀ (cX / β) (ξ ν) := by
    intro ν hν
    refine ⟨hL, hγr.1, by positivity, ?_, fun k => ?_⟩
    · have : cX / β * q / (1 - q) = cX * q / (1 - q) / β := by field_simp
      rw [this, div_le_iff₀ hβpos]
      have h := hβ2
      rw [div_le_iff₀ h1q] at h
      have : cX * q / (1 - q) * 2 ≤ β := by
        rw [div_mul_eq_mul_div, div_le_iff₀ h1q]; linarith
      linarith
    · have := h1.1 ν hν k
      refine this.trans (le_of_eq ?_)
      ring
  -- the limits along the tori (Step A)
  have hlim : ∀ ν : ℝ, ∃ (m : ℝ) (Gt Gl : (Fin d → ℤ) → ℝ), ν ∈ Set.Ioc (0 : ℝ) 1 →
      LimAlong (M * L) (fun ℓ _ => blockM d N ℓ hN β ν) m ∧
      (∀ z, LimAlong (M * L) (fun ℓ _ => blockGtr d N ℓ hN β ν (embedZ ℓ z)) (Gt z)) ∧
      (∀ z, LimAlong (M * L) (fun ℓ _ => blockGlg d N ℓ hN β ν (embedZ ℓ z)) (Gl z)) := by
    intro ν
    by_cases hν : ν ∈ Set.Ioc (0 : ℝ) 1
    · obtain ⟨kf, -, -, T, hT⟩ := hF β hβF ν hν.1 hν.2 _ (norm_single_idx hN)
      obtain ⟨m, Gt, Gl, h⟩ := exists_limits hN hT hd hδ hL hM
      exact ⟨m, Gt, Gl, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h hν⟩
  choose m Gtr Glg hlim' using hlim
  refine ⟨m, Gtr, Glg, ?_, ?_, ?_⟩
  · intro ν hν0 hν1 h hh x y ε hε
    obtain ⟨hm, hGt, hGl⟩ := hlim' ν ⟨hν0, hν1⟩
    exact bullet_one hN hm hGt hGl h hh x y ε hε
  · intro ν hν0 hν1
    exact bounds_pos_nu hL hM hβ1 hρ₀r.1 hcS.le hρ₁r.1 hρ₁r.2 HS
      (fun ν hν => (hJb ν hν).2) h2 h3 H HL hC1nn hC1
      (fun ν hν => (hlim' ν hν).1) (fun ν hν => (hlim' ν hν).2.1)
      (fun ν hν => (hlim' ν hν).2.2) (c := c) (c' := c')
      (by linarith) (by linarith) (min_le_left _ _) (min_le_right _ _) ν ⟨hν0, hν1⟩
  · exact limits_zero hd hL hM hβ1 hρ₀r.1 hcS.le hρ₁r.1 hρ₁r.2 ha hcP.le hcX.le HS h1.2
      hJt (fun ν hν => (hJb ν hν).2) h2 h3 H HL hC2 hC2nn (fun ν hν => (hlim' ν hν).1) (fun ν hν => (hlim' ν hν).2.1)
      (fun ν hν => (hlim' ν hν).2.2) (c := c) (by linarith) (by linarith) (by linarith)

theorem decay_term_weaken {d j : ℕ} {L C C' δ δ' r τ : ℝ} (hL : 0 < L) (hr : 0 ≤ r)
    (hC0 : 0 ≤ C) (hC : C ≤ C') (hδ : δ' ≤ δ)
    (h : τ ≤ C * (L ^ (j * (d - 2)))⁻¹ * Real.exp (-(δ * r / L ^ j))) :
    τ ≤ C' * (L ^ (j * (d - 2)))⁻¹ * Real.exp (-(δ' * r / L ^ j)) := by
  refine h.trans ?_
  have hA : 0 ≤ (L ^ (j * (d - 2)))⁻¹ := by positivity
  have hLj : 0 < L ^ j := by positivity
  have hex : Real.exp (-(δ * r / L ^ j)) ≤ Real.exp (-(δ' * r / L ^ j)) := by
    refine Real.exp_le_exp.2 ?_
    have : δ' * r / L ^ j ≤ δ * r / L ^ j := by gcongr
    linarith
  have := Real.exp_pos (-(δ' * r / L ^ j))
  calc _ ≤ C * (L ^ (j * (d - 2)))⁻¹ * Real.exp (-(δ' * r / L ^ j)) :=
        mul_le_mul_of_nonneg_left hex (by positivity)
    _ ≤ _ := by gcongr

theorem KernelDecay.weaken {d : ℕ} {L C C' δ δ' r : ℝ} {t : ℕ → ℝ} (hL : 0 < L) (hr : 0 ≤ r)
    (hC0 : 0 ≤ C) (hC : C ≤ C') (hδ : δ' ≤ δ) (h : KernelDecay d L C δ r t) :
    KernelDecay d L C' δ' r t := fun j => decay_term_weaken hL hr hC0 hC hδ (h j)

theorem KernelMassDecay.nonneg {d L : ℕ} (hL : 1 ≤ L) {C δ : ℝ}
    {t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ} (h : KernelMassDecay d L C δ t) : 0 ≤ C := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
  have h2 : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have := h 0 1 one_pos (by norm_num; nlinarith) 0 0
  simpa using (abs_nonneg _).trans this

theorem KernelMassDecay.weaken {d L : ℕ} (hL : 1 ≤ L) {C C' δ δ' : ℝ}
    {t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ} (h : KernelMassDecay d L C δ t) (hC : C ≤ C')
    (hδ : δ' ≤ δ) : KernelMassDecay d L C' δ' t := by
  have hC0 := h.nonneg hL
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  intro j μ hμ hμ2 x y
  exact decay_term_weaken (d := d) hL0 (norm_nonneg _) hC0 hC hδ (h j μ hμ hμ2 x y)

/-- Corollary: the large-mass facts may come with their own constants `C_G', δ_G'` (for the same
kernel family `t`). -/
theorem rootC_of_rootF_c1Star_kernelLarge (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N)
    (hjoint : RootFAndC1Star d N hN)
    (hG : ∀ (L : ℕ) [NeZero L] (a : ℝ), 3 ≤ L → 1 / (2 * (1 - ((L : ℝ) ^ 2)⁻¹)) < a →
      a < 3 / 2 → ∃ (t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
        (t0 : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (C_G δ_G C_P C' δ' : ℝ),
        KernelHyp d L a t t0 C_G δ_G C_P ∧ KernelHypLarge d L a t C' δ') :
    RootCStatement d N := by
  refine rootC_of_rootF_c1Star d N hd hN hjoint fun L _ a hL ha1 ha2 => ?_
  obtain ⟨t, t0, C_G, δ_G, C_P, C', δ', H, HL⟩ := hG L a hL ha1 ha2
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : 1 ≤ L := by omega
  refine ⟨t, t0, max C_G C', min δ_G δ', C_P, ?_, ?_⟩
  · refine { H with g2 := fun x y => ?_, nonneg_G := ?_, pos_δ := ?_ }
    · exact KernelDecay.weaken hL0 (norm_nonneg _) H.nonneg_G (le_max_left _ _)
        (min_le_left _ _) (H.g2 x y)
    · exact H.nonneg_G.trans (le_max_left _ _)
    · exact lt_min H.pos_δ HL.pos_δ
  · refine ⟨HL.g1, HL.g2.weaken hL1 (le_max_right _ _) (min_le_right _ _),
      lt_min H.pos_δ HL.pos_δ⟩

end Balaban.Correlations
