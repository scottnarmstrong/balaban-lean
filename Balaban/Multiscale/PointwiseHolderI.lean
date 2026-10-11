/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.Pointwise48
public import Balaban.Multiscale.PointwiseHolderArith
public import Balaban.Green.Lattice.LocHolder
public import Balaban.Green.Lattice.HolderSums

/-!
# Proposition 4.9, Case 2: Lemma Loc (c) on the lifted ball

* `loc_lift_c`: Lemma Loc (c) for a lifted torus field;
* `PtSetting.holder_caseI`: for `x` in layer `j₀ + 1` with `ρ = c₀ L^{j₀}/d ≥ 8` and a lattice
  vector `z` with `1 ≤ ‖z‖ ≤ ρ/4`,
  `ℓ² |∂u(x + z) - ∂u(x)| ≤ (K₁/θ) ℓ^θ ‖z‖^{1-θ} e^{-(ε₀/2)t} ℓ_{j'}² ‖f‖_∞ +
    (K₂/θ) ℓ^θ ‖z‖^{1-θ} M`
  where `M` bounds `U` on the `(2d+1)`-neighbourhood of `x`.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban Balaban.LatticeGreen

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- Lemma Loc (c) for a lifted torus field, centred at the lift centre. -/
theorem loc_lift_c (hd : 3 ≤ d) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧
      ∀ {L N₀ k : ℕ} [NeZero N₀] [NeZero L] (c : Torus d (N₀ * L ^ k))
        (v : Torus d (N₀ * L ^ k) → ℂ) {ρ : ℝ}, 8 ≤ ρ → ∀ (z : Fin d → ℤ) {r : ℝ},
        ‖z‖ ≤ r → r ≤ ρ / 4 → ∀ ν : Fin d,
        ‖(v (liftPt c z + Pi.single ν 1) - v (liftPt c z)) - (v (c + Pi.single ν 1) - v c)‖ ≤
          Cc * r * ρ ^ (-2 - (d : ℝ) / 2) *
            Real.sqrt (∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * ρ), ‖v (liftPt c w)‖ ^ 2) +
          ∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * ρ),
            |greenDiff d ν (z - w) - greenDiff d ν (0 - w)| *
              ‖negLap (fun w => v (liftPt c w)) w‖ := by
  obtain ⟨C, hC, h⟩ := lemma_loc_c hd
  refine ⟨C, hC, fun {L N₀ k} _ _ c v {ρ} hρ z {r} hzr hrρ ν => ?_⟩
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hzr
  have h' := h ρ hρ 0 z 0 (by simp only [sub_zero]; linarith) (by simp only [sub_self, norm_zero]; linarith)
    r (by simpa using hzr) hrρ ν (fun w => v (liftPt c w))
    (fun w => negLap (fun w => v (liftPt c w)) w) (fun z _ => rfl)
  have e : liftPt c (Pi.single ν 1) = c + Pi.single ν 1 := by
    have := liftPt_add_single c 0 ν
    rwa [zero_add, liftPt_zero] at this
  simp only [zero_add, liftPt_add_single, liftPt_zero, e] at h'
  exact h'

/-- The constant of the `ℓ²` part (`PtSetting.l2_part`). -/
def holderKl2 (d L : ℕ) (c0 : ℝ) : ℝ :=
  2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) * (L : ℝ) ^ 2 * bd d L ^ 2 /
    Real.sqrt ((c0 / d) ^ d)

theorem holderKl2_nonneg (d L : ℕ) (c0 : ℝ) : 0 ≤ holderKl2 d L c0 := by
  unfold holderKl2
  have : 0 ≤ poincareConst d := le_min (by positivity) (by norm_num)
  have : 0 ≤ bd d L := Real.sqrt_nonneg _
  positivity

namespace PtSetting

variable {G : GeneratingSet d L N₀ k ϱ} (S : PtSetting G)

/-- **Proposition 4.9, Case 2: the decomposition.**  Splits the Loc (c) bound into the `ℓ²` part,
the source part and the potential part. -/
theorem holder_caseI_pre
    {Cc cH c0 : ℝ} (hc0 : 0 < c0)
    (hc04 : c0 ≤ 1 / 4) {j₀ : ℕ} (hj01 : 1 ≤ j₀) (hjk : j₀ + 1 ≤ k)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer (j₀ + 1)) (hρ : 8 ≤ c0 * (L : ℝ) ^ j₀ / d)
    {z : Fin d → ℤ} (hz1 : 1 ≤ ‖z‖) (hzρ : ‖z‖ ≤ (c0 * (L : ℝ) ^ j₀ / d) / 4)
    {θ : ℝ} (ν : Fin d)
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖S.f i‖ ≤ Mf)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist x S.y')
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ q ∈ G.Ω 1, G.pathDist q x ≤ ENNReal.ofReal (2 * d + 1) → S.U q ≤ M)
    (hLc : ‖(S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
        (S.ut (x + Pi.single ν 1) - S.ut x)‖ ≤
      Cc * ‖z‖ * (c0 * (L : ℝ) ^ j₀ / d) ^ (-2 - (d : ℝ) / 2) *
        Real.sqrt (∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * (c0 * (L : ℝ) ^ j₀ / d)),
          ‖S.ut (liftPt x w)‖ ^ 2) +
      ∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * (c0 * (L : ℝ) ^ j₀ / d)),
        |greenDiff d ν (z - w) - greenDiff d ν (0 - w)| *
          ‖negLap (fun w => S.ut (liftPt x w)) w‖)
    (hH : ∀ {R : ℝ}, 0 ≤ R → ∀ A : Finset (Fin d → ℤ),
      A.card ≤ (latticeBall (0 : Fin d → ℤ) R).card →
      ∑ w ∈ A, |greenDiff d ν (0 - w + z) - greenDiff d ν (0 - w)| ≤
        cH / θ * (‖z‖ + ‖z‖ ^ (1 - θ) * (R + 1) ^ θ)) :
    ∃ Tv SA Sb : ℝ,
      ‖(S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
          (S.ut (x + Pi.single ν 1) - S.ut x)‖ ≤
        Cc * ‖z‖ * ((c0 * (L : ℝ) ^ j₀ / d) ^ 2)⁻¹ * Tv +
          (Mf * SA + 4 * (((L : ℝ) ^ j₀) ^ 2)⁻¹ * M * Sb) ∧
      Tv ≤ holderKl2 d L c0 * Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf) ∧
      SA ≤ cH / θ * (‖z‖ + ‖z‖ ^ (1 - θ) * ((((L ^ S.j' : ℕ)) : ℝ) + 1) ^ θ) ∧
      Sb ≤ cH / θ * (‖z‖ + ‖z‖ ^ (1 - θ) * (2 * (c0 * (L : ℝ) ^ j₀ / d) + 1) ^ θ) ∧
      (SA = 0 ∨ ((L : ℝ) ^ (j₀ + 1) ≤ L * (L : ℝ) ^ S.j' ∧
        1 ≤ Real.exp (agmonRate d / 2 * (2 * d + 1)) * Real.exp (-(agmonRate d / 2 * t)))) := by
  have hc := poincareConst_pos S.hd0
  have hε0 := agmonRate_pos S.hd0
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast S.hd0
  have hd0 : (0 : ℝ) < d := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hLc0 : (0 : ℝ) < (L : ℝ) ^ j₀ := by positivity
  have hj2 : 2 ≤ j₀ + 1 := by omega
  set ρ := c0 * (L : ℝ) ^ j₀ / d with hρdef
  have hρ0 : 0 < ρ := by linarith
  set r := ‖z‖ with hrdef
  have hr0 : 0 < r := by linarith
  set ℓ : ℝ := (L : ℝ) ^ (j₀ + 1) with hℓdef
  have hℓ0 : 0 < ℓ := by positivity
  have hℓeq : ℓ = L * (L : ℝ) ^ j₀ := by rw [hℓdef, pow_succ']
  have hρL : ρ ≤ (L : ℝ) ^ j₀ := by
    rw [hρdef, div_le_iff₀ hd0]
    nlinarith
  have hρℓ : ρ ≤ ℓ := by
    rw [hℓeq]; nlinarith
  have hrρ : r ≤ ρ := by linarith
  have hrℓ : r ≤ ℓ := hrρ.trans hρℓ
  have hκ : ℓ = (d * L / c0) * ρ := by
    rw [hℓeq, hρdef]; field_simp
  have hRd : (d : ℝ) * (2 * ρ) ≤ (L : ℝ) ^ j₀ := by
    rw [hρdef]; field_simp; nlinarith
  set ball := latticeBall (0 : Fin d → ℤ) (2 * ρ) with hball
  have hzb : ∀ w ∈ ball, (d : ℝ) * ‖w‖ ≤ (L : ℝ) ^ (j₀ + 1 - 1) := by
    intro w hw
    have := (mem_latticeBall (by positivity)).1 hw
    rw [sub_zero] at this
    simp only [Nat.add_sub_cancel]
    exact (mul_le_mul_of_nonneg_left this (Nat.cast_nonneg d)).trans hRd
  set m := 4 * (((L : ℝ) ^ j₀) ^ 2)⁻¹ * M with hm
  have hm0 : 0 ≤ m := by positivity
  have hM' : ∀ q ∈ G.Ω 1, G.pathDist q x ≤ ENNReal.ofReal (2 * d + 1) → ‖S.ut q‖ ≤ M :=
    fun q hq h => (S.norm_ut_le_U q).trans (hM q hq h)
  have hg : ∀ w ∈ ball, ‖negLap (fun w => S.ut (liftPt x w)) w‖ ≤ ‖S.ft (liftPt x w)‖ + m := by
    intro w hw
    have := S.g_bound hj2 hjk hx (hzb w hw) hM0 hM'
    simpa only [Nat.add_sub_cancel] using this
  have hT := S.l2_part hc0 hc04 hj2 hjk hx (by simpa using hρ) hMf0 hMf ht0 ht
  simp only [Nat.add_sub_cancel] at hT
  set Tv := ρ ^ (-(d : ℝ) / 2) * Real.sqrt (∑ w ∈ ball, ‖S.ut (liftPt x w)‖ ^ 2) with hTv
  set Kl2 : ℝ := 2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) * (L : ℝ) ^ 2 *
    bd d L ^ 2 / Real.sqrt ((c0 / d) ^ d) with hKl2
  set e : ℝ := Real.exp (-(agmonRate d / 2 * t)) with hedef
  have he0 : 0 < e := Real.exp_pos _
  set F : ℝ := (L : ℝ) ^ (2 * S.j') * Mf with hFdef
  have hF0 : 0 ≤ F := by positivity
  have hTv' : Tv ≤ Kl2 * e * F := hT
  obtain ⟨A, hAsub, hAcard, hAvan, hAne⟩ := S.fsum_data hj2 hjk hx (R := 2 * ρ) (by positivity)
    (by simpa only [Nat.add_sub_cancel] using hRd)
  -- the kernel sums
  set Kf : (Fin d → ℤ) → ℝ := fun w =>
    |greenDiff d ν (0 - w + z) - greenDiff d ν (0 - w)| with hKf
  have hKf0 : ∀ w, 0 ≤ Kf w := fun w => abs_nonneg _
  have hKeq : ∀ w, |greenDiff d ν (z - w) - greenDiff d ν (0 - w)| = Kf w := by
    intro w
    simp only [hKf]
    have : z - w = 0 - w + z := by abel
    rw [this]
  -- sum over the ball
  have hSb : ∑ w ∈ ball, Kf w ≤ cH / θ * (r + r ^ (1 - θ) * (2 * ρ + 1) ^ θ) :=
    hH (by positivity) ball le_rfl
  -- the source part
  set Rf : ℝ := (((L ^ S.j' : ℕ)) : ℝ) with hRf
  have hRf0 : 0 ≤ Rf := Nat.cast_nonneg _
  have hAcard' : A.card ≤ (latticeBall (0 : Fin d → ℤ) Rf).card := by
    rw [hRf, card_latticeBall_nat]
    exact hAcard.trans (Nat.pow_le_pow_left (by omega) d)
  have hSA : ∑ w ∈ A, Kf w ≤ cH / θ * (r + r ^ (1 - θ) * (Rf + 1) ^ θ) :=
    hH hRf0 A hAcard'
  have hsplit : ∑ w ∈ ball, Kf w * ‖negLap (fun w => S.ut (liftPt x w)) w‖ ≤
      Mf * ∑ w ∈ A, Kf w + m * ∑ w ∈ ball, Kf w := by
    calc _ ≤ ∑ w ∈ ball, Kf w * (‖S.ft (liftPt x w)‖ + m) :=
          Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left (hg w hw) (hKf0 w)
      _ = ∑ w ∈ ball, Kf w * ‖S.ft (liftPt x w)‖ + m * ∑ w ∈ ball, Kf w := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun w _ => by ring
      _ ≤ _ := by
          refine add_le_add ?_ le_rfl
          have h1 : ∑ w ∈ ball, Kf w * ‖S.ft (liftPt x w)‖ =
              ∑ w ∈ A, Kf w * ‖S.ft (liftPt x w)‖ :=
            (Finset.sum_subset hAsub (fun w hw hnA => by rw [hAvan w hw hnA]; simp)).symm
          rw [h1, Finset.mul_sum]
          refine Finset.sum_le_sum fun w _ => ?_
          rw [mul_comm Mf]
          exact mul_le_mul_of_nonneg_left (S.norm_ft_le hMf0 hMf _) (hKf0 w)
  -- the main chain
  have hmain : ‖(S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
        (S.ut (x + Pi.single ν 1) - S.ut x)‖ ≤
      Cc * r * (ρ ^ 2)⁻¹ * Tv + (Mf * ∑ w ∈ A, Kf w + m * ∑ w ∈ ball, Kf w) := by
    refine hLc.trans ?_
    have e1 : Cc * r * ρ ^ (-2 - (d : ℝ) / 2) *
        Real.sqrt (∑ w ∈ ball, ‖S.ut (liftPt x w)‖ ^ 2) = Cc * r * (ρ ^ 2)⁻¹ * Tv := by
      rw [rpow_neg_two_sub_half hρ0 d, hTv]; ring
    have e2 : ∑ w ∈ ball, |greenDiff d ν (z - w) - greenDiff d ν (0 - w)| *
        ‖negLap (fun w => S.ut (liftPt x w)) w‖ =
        ∑ w ∈ ball, Kf w * ‖negLap (fun w => S.ut (liftPt x w)) w‖ :=
      Finset.sum_congr rfl fun w _ => by rw [hKeq]
    rw [e1, e2]
    linarith
  refine ⟨Tv, ∑ w ∈ A, Kf w, ∑ w ∈ ball, Kf w, hmain, hTv', hSA, hSb, ?_⟩
  by_cases hAn : A.Nonempty
  · obtain ⟨hpd, hjj⟩ := hAne hAn
    right
    have ht_le : t ≤ 2 * d + 1 := by
      have := ht.trans hpd
      rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    refine ⟨?_, ?_⟩
    · rw [hℓdef, pow_succ']
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by omega)) hL0.le
    · rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
  · left
    rw [Finset.not_nonempty_iff_eq_empty.1 hAn]
    simp

/-- **Proposition 4.9, Case 2.** -/
theorem holder_caseI
    {Cc cH c0 : ℝ} (hCc : 0 ≤ Cc) (hcH : 0 ≤ cH) (hc0 : 0 < c0)
    (hc04 : c0 ≤ 1 / 4) {j₀ : ℕ} (hj01 : 1 ≤ j₀) (hjk : j₀ + 1 ≤ k)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer (j₀ + 1)) (hρ : 8 ≤ c0 * (L : ℝ) ^ j₀ / d)
    {z : Fin d → ℤ} (hz1 : 1 ≤ ‖z‖) (hzρ : ‖z‖ ≤ (c0 * (L : ℝ) ^ j₀ / d) / 4)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (ν : Fin d)
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖S.f i‖ ≤ Mf)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist x S.y')
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ q ∈ G.Ω 1, G.pathDist q x ≤ ENNReal.ofReal (2 * d + 1) → S.U q ≤ M)
    (hLc : ‖(S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
        (S.ut (x + Pi.single ν 1) - S.ut x)‖ ≤
      Cc * ‖z‖ * (c0 * (L : ℝ) ^ j₀ / d) ^ (-2 - (d : ℝ) / 2) *
        Real.sqrt (∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * (c0 * (L : ℝ) ^ j₀ / d)),
          ‖S.ut (liftPt x w)‖ ^ 2) +
      ∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * (c0 * (L : ℝ) ^ j₀ / d)),
        |greenDiff d ν (z - w) - greenDiff d ν (0 - w)| *
          ‖negLap (fun w => S.ut (liftPt x w)) w‖)
    (hH : ∀ {R : ℝ}, 0 ≤ R → ∀ A : Finset (Fin d → ℤ),
      A.card ≤ (latticeBall (0 : Fin d → ℤ) R).card →
      ∑ w ∈ A, |greenDiff d ν (0 - w + z) - greenDiff d ν (0 - w)| ≤
        cH / θ * (‖z‖ + ‖z‖ ^ (1 - θ) * (R + 1) ^ θ)) :
    ((L : ℝ) ^ (j₀ + 1)) ^ 2 * ‖(S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
        (S.ut (x + Pi.single ν 1) - S.ut x)‖ ≤
      ((Cc * (d * L / c0) ^ 2 * holderKl2 d L c0 +
        3 * (L : ℝ) ^ 2 * cH * Real.exp (agmonRate d / 2 * (2 * d + 1))) / θ) *
        (((L : ℝ) ^ (j₀ + 1)) ^ θ * ‖z‖ ^ (1 - θ)) *
        (Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf)) +
      (16 * (L : ℝ) ^ 2 * cH / θ) * (((L : ℝ) ^ (j₀ + 1)) ^ θ * ‖z‖ ^ (1 - θ)) * M := by
  obtain ⟨Tv, SA, Sb, hmain, hTv, hSA, hSb, hsrc⟩ := S.holder_caseI_pre hc0 hc04 hj01 hjk hx
    hρ hz1 hzρ ν hMf0 hMf ht0 ht hM0 hM hLc hH
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast S.hd0
  have hd0 : (0 : ℝ) < d := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hLc0 : (0 : ℝ) < (L : ℝ) ^ j₀ := by positivity
  have hρ0 : 0 < c0 * (L : ℝ) ^ j₀ / d := by
    have : 0 < c0 * (L : ℝ) ^ j₀ := by positivity
    positivity
  have hρL : c0 * (L : ℝ) ^ j₀ / d ≤ (L : ℝ) ^ j₀ := by
    rw [div_le_iff₀ hd0]
    nlinarith
  have hρℓ : c0 * (L : ℝ) ^ j₀ / d ≤ (L : ℝ) ^ (j₀ + 1) := by
    rw [pow_succ']; nlinarith
  have hLj'1 : (1 : ℝ) ≤ (L : ℝ) ^ S.j' := one_le_pow₀ hL1
  have hRf1 : (((L ^ S.j' : ℕ)) : ℝ) + 1 ≤ 2 * (L : ℝ) ^ S.j' := by push_cast; linarith
  have hκ : (L : ℝ) ^ (j₀ + 1) = (d * L / c0) * (c0 * (L : ℝ) ^ j₀ / d) := by
    rw [pow_succ']; field_simp
  exact holder_assemble (Dn := ‖(S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
        (S.ut (x + Pi.single ν 1) - S.ut x)‖) (Tv := Tv) (SA := SA) (Sb := Sb)
    (F := (L : ℝ) ^ (2 * S.j') * Mf) (m := 4 * (((L : ℝ) ^ j₀) ^ 2)⁻¹ * M)
    hCc hcH hθ0 hθ1.le (by linarith) (by linarith) hρℓ (by linarith) hκ (by rw [pow_succ']) hL0 hL1 hLc0
    hLj'1 hMf0 hM0 rfl (Real.exp_pos _) (by rw [pow_mul']) (holderKl2_nonneg d L c0)
    (Real.exp_pos _).le hmain hTv hSA hRf1 (Nat.cast_nonneg _) hSb hsrc

end PtSetting

end Balaban.Multiscale
