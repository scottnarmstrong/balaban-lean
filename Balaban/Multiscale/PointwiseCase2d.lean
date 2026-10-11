/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseCase2c

/-!
# Lemma P, Case 2: assembly

`case2_bound`: for `x` in layer `j = j₀ + 1` with `ρ = c₀ L^{j₀}/d ≥ 8`,
`U(x) ≤ K e^{-(ε₀/2) t} ℓ_{j'}² ‖f‖_∞ + c_G (36 + 12 L) c₀ M`, where `M` bounds `U` on the
`(2d+1)`-neighbourhood of `x`.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban Balaban.LatticeGreen

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem pot_arith {cG c0 L d M Lc : ℝ} (hcG : 0 ≤ cG) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hL : 1 ≤ L) (hd : 1 ≤ d) (hLc : 0 < Lc) (hM : 0 ≤ M) (hρ : 1 ≤ c0 * Lc / d) :
    (4 * (Lc ^ 2)⁻¹ * M) * (cG * (2 * (c0 * Lc / d) + 1) ^ 2) +
      (Lc * L) * d * ((4 * (Lc ^ 2)⁻¹ * M) * (cG * (2 * (c0 * Lc / d) + 1))) ≤
        cG * (36 + 12 * L) * c0 * M := by
  set ρ := c0 * Lc / d with hρd
  have hd0 : 0 < d := by linarith
  have hρ0 : 0 < ρ := by linarith
  have h3 : 2 * ρ + 1 ≤ 3 * ρ := by nlinarith
  have h3' : 0 ≤ 2 * ρ + 1 := by linarith
  have hm : 0 ≤ 4 * (Lc ^ 2)⁻¹ * M := by positivity
  have e1 : (2 * ρ + 1) ^ 2 ≤ (3 * ρ) ^ 2 := pow_le_pow_left₀ h3' h3 2
  have a1 : (4 * (Lc ^ 2)⁻¹ * M) * (cG * (2 * ρ + 1) ^ 2) ≤
      (4 * (Lc ^ 2)⁻¹ * M) * (cG * (3 * ρ) ^ 2) := by gcongr
  have a2 : (Lc * L) * d * ((4 * (Lc ^ 2)⁻¹ * M) * (cG * (2 * ρ + 1))) ≤
      (Lc * L) * d * ((4 * (Lc ^ 2)⁻¹ * M) * (cG * (3 * ρ))) := by gcongr
  refine (add_le_add a1 a2).trans ?_
  have hρe : ρ * d = c0 * Lc := by rw [hρd]; field_simp
  have e2 : (4 * (Lc ^ 2)⁻¹ * M) * (cG * (3 * ρ) ^ 2) = 36 * cG * M * c0 ^ 2 / d ^ 2 := by
    rw [hρd]; field_simp; ring
  have e3 : (Lc * L) * d * ((4 * (Lc ^ 2)⁻¹ * M) * (cG * (3 * ρ))) = 12 * cG * M * L * c0 := by
    rw [hρd]; field_simp; ring
  rw [e2, e3]
  have e4 : 36 * cG * M * c0 ^ 2 / d ^ 2 ≤ 36 * cG * M * c0 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : c0 ^ 2 ≤ c0 := by nlinarith
    have hd2 : (1 : ℝ) ≤ d ^ 2 := one_le_pow₀ hd
    have h2 : c0 ≤ c0 * d ^ 2 := by nlinarith
    have : c0 ^ 2 ≤ c0 * d ^ 2 := h1.trans h2
    have h36 : 0 ≤ 36 * cG * M := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h36]
  nlinarith

theorem rpow_neg_one_sub_half {ρ : ℝ} (hρ : 0 < ρ) (d : ℕ) :
    ρ ^ (-1 - (d : ℝ) / 2) = ρ⁻¹ * ρ ^ (-(d : ℝ) / 2) := by
  have : (-1 - (d : ℝ) / 2) = -1 + (-(d : ℝ) / 2) := by ring
  rw [this, Real.rpow_add hρ, Real.rpow_neg_one]

namespace PtSetting

variable {G : GeneratingSet d L N₀ k ϱ} (S : PtSetting G)

theorem case2_fpart {cG c0 : ℝ} (hcG : 0 ≤ cG) (hc0 : 0 < c0) (hc04 : c0 ≤ 1 / 4)
    {j₀ : ℕ} (hj01 : 1 ≤ j₀) (hjk : j₀ + 1 ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer (j₀ + 1)) {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖S.f i‖ ≤ Mf)
    {t : ℝ} (ht : ENNReal.ofReal t ≤ G.pathDist x S.y')
    (hG : ∀ R : ℝ, 0 ≤ R → ∀ A : Finset (Fin d → ℤ),
      A.card ≤ (latticeBall (0 : Fin d → ℤ) R).card →
      (∑ z ∈ A, latticeGreen d (0 - z) ≤ cG * (R + 1) ^ 2) ∧
      (∀ ν : Fin d, ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| ≤
        cG * (R + 1)))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hRd : (d : ℝ) * (2 * ρ) ≤ (L : ℝ) ^ j₀) :
    ∃ A : Finset (Fin d → ℤ), 
      (∀ F : (Fin d → ℤ) → ℝ, (∀ z, 0 ≤ F z) →
        ∑ z ∈ latticeBall (0 : Fin d → ℤ) (2 * ρ), F z * ‖S.ft (liftPt x z)‖ ≤
          Mf * ∑ z ∈ A, F z) ∧
      (Mf * ∑ z ∈ A, latticeGreen d (0 - z) + (L : ℝ) ^ (j₀ + 1) *
        ∑ ν : Fin d, (Mf * ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) -
          latticeGreen d (0 - z)|) ≤
        cG * (4 + 2 * d * L) * Real.exp (agmonRate d / 2 * (2 * d + 1)) *
          Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf)) := by
  have hε0 := agmonRate_pos S.hd0
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast S.hd0
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hj2 : 2 ≤ j₀ + 1 := by omega
  obtain ⟨A, hAsub, hAcard, hAvan, hAne⟩ := S.fsum_data hj2 hjk hx (R := 2 * ρ) (by positivity)
    (by simpa only [Nat.add_sub_cancel] using hRd)
  refine ⟨A, ?_, ?_⟩
  · intro F hF
    have h1 : ∑ z ∈ latticeBall (0 : Fin d → ℤ) (2 * ρ), F z * ‖S.ft (liftPt x z)‖ =
        ∑ z ∈ A, F z * ‖S.ft (liftPt x z)‖ :=
      (Finset.sum_subset hAsub (fun z hz hnA => by rw [hAvan z hz hnA]; simp)).symm
    rw [h1, Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    rw [mul_comm Mf]
    exact mul_le_mul_of_nonneg_left (S.norm_ft_le hMf0 hMf _) (hF z)
  · set Rf : ℝ := (((L ^ S.j' : ℕ)) : ℝ) with hRf
    have hRf0 : 0 ≤ Rf := Nat.cast_nonneg _
    have hAcard' : A.card ≤ (latticeBall (0 : Fin d → ℤ) Rf).card := by
      rw [hRf, card_latticeBall_nat]
      exact hAcard.trans (Nat.pow_le_pow_left (by omega) d)
    obtain ⟨hGA, hGAν⟩ := hG Rf hRf0 A hAcard'
    have hnn : 0 ≤ cG * (4 + 2 * d * L) * Real.exp (agmonRate d / 2 * (2 * d + 1)) *
        Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf) := by positivity
    by_cases hAn : A.Nonempty
    · obtain ⟨hpd, hjj⟩ := hAne hAn
      have ht_le : t ≤ 2 * d + 1 := by
        have := ht.trans hpd
        rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
      have hexpo : 1 ≤ Real.exp (agmonRate d / 2 * (2 * d + 1)) *
          Real.exp (-(agmonRate d / 2 * t)) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith
      have hLj1 : (1 : ℝ) ≤ (L : ℝ) ^ S.j' := one_le_pow₀ hL1
      have hRf1 : Rf + 1 ≤ 2 * (L : ℝ) ^ S.j' := by rw [hRf]; push_cast; linarith
      have hLjj : (L : ℝ) ^ (j₀ + 1) ≤ (L : ℝ) * (L : ℝ) ^ S.j' := by
        rw [← pow_succ']
        exact pow_le_pow_right₀ hL1 hjj
      have hsC : ∑ z ∈ A, latticeGreen d (0 - z) ≤ cG * (4 * ((L : ℝ) ^ S.j') ^ 2) :=
        hGA.trans (calc cG * (Rf + 1) ^ 2 ≤ cG * (2 * (L : ℝ) ^ S.j') ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hRf1 2) hcG
          _ = _ := by ring)
      have hsD : ∀ ν : Fin d, ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) -
          latticeGreen d (0 - z)| ≤ cG * (2 * (L : ℝ) ^ S.j') := fun ν =>
        (hGAν ν).trans (mul_le_mul_of_nonneg_left hRf1 hcG)
      have h1 : Mf * ∑ z ∈ A, latticeGreen d (0 - z) ≤ Mf * (cG * (4 * ((L : ℝ) ^ S.j') ^ 2)) :=
        mul_le_mul_of_nonneg_left hsC hMf0
      have h2 : ∑ ν : Fin d, (Mf * ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) -
          latticeGreen d (0 - z)|) ≤ d * (Mf * (cG * (2 * (L : ℝ) ^ S.j'))) := by
        calc _ ≤ ∑ _ν : Fin d, (Mf * (cG * (2 * (L : ℝ) ^ S.j'))) :=
              Finset.sum_le_sum fun ν _ => mul_le_mul_of_nonneg_left (hsD ν) hMf0
          _ = _ := by simp
      have h3 : (L : ℝ) ^ (j₀ + 1) * ∑ ν : Fin d, (Mf * ∑ z ∈ A, |latticeGreen d (0 - z +
          Pi.single ν 1) - latticeGreen d (0 - z)|) ≤
          ((L : ℝ) * (L : ℝ) ^ S.j') * (d * (Mf * (cG * (2 * (L : ℝ) ^ S.j')))) :=
        mul_le_mul hLjj h2 (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
      have h4 : (L : ℝ) ^ (2 * S.j') = ((L : ℝ) ^ S.j') ^ 2 := by rw [pow_mul']
      have h5 : Mf * (cG * (4 * ((L : ℝ) ^ S.j') ^ 2)) + ((L : ℝ) * (L : ℝ) ^ S.j') *
          (d * (Mf * (cG * (2 * (L : ℝ) ^ S.j')))) =
          cG * (4 + 2 * d * L) * ((L : ℝ) ^ (2 * S.j') * Mf) := by rw [h4]; ring
      calc _ ≤ Mf * (cG * (4 * ((L : ℝ) ^ S.j') ^ 2)) + ((L : ℝ) * (L : ℝ) ^ S.j') *
            (d * (Mf * (cG * (2 * (L : ℝ) ^ S.j')))) := add_le_add h1 h3
        _ = cG * (4 + 2 * d * L) * ((L : ℝ) ^ (2 * S.j') * Mf) := h5
        _ = cG * (4 + 2 * d * L) * ((L : ℝ) ^ (2 * S.j') * Mf) * 1 := by ring
        _ ≤ cG * (4 + 2 * d * L) * ((L : ℝ) ^ (2 * S.j') * Mf) *
            (Real.exp (agmonRate d / 2 * (2 * d + 1)) * Real.exp (-(agmonRate d / 2 * t))) :=
            mul_le_mul_of_nonneg_left hexpo (by positivity)
        _ = _ := by ring
    · rw [Finset.not_nonempty_iff_eq_empty.1 hAn]
      simpa using hnn

theorem case2_bound {Ca Cb cG c0 : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hcG : 0 ≤ cG)
    (hc0 : 0 < c0) (hc04 : c0 ≤ 1 / 4)
    {j₀ : ℕ} (hj01 : 1 ≤ j₀) (hjk : j₀ + 1 ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer (j₀ + 1)) (hρ : 8 ≤ c0 * (L : ℝ) ^ j₀ / d)
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖S.f i‖ ≤ Mf)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist x S.y')
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ G.Ω 1, G.pathDist z x ≤ ENNReal.ofReal (2 * d + 1) → S.U z ≤ M)
    (hLa : ‖S.ut x‖ ≤ Ca * (c0 * (L : ℝ) ^ j₀ / d) ^ (-(d : ℝ) / 2) *
        Real.sqrt (∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * (c0 * (L : ℝ) ^ j₀ / d)),
          ‖S.ut (liftPt x w)‖ ^ 2) +
        ∑ z ∈ latticeBall (0 : Fin d → ℤ) (2 * (c0 * (L : ℝ) ^ j₀ / d)),
          latticeGreen d (0 - z) * ‖negLap (fun w => S.ut (liftPt x w)) z‖)
    (hLb : ∀ ν : Fin d, ‖S.ut (x + Pi.single ν 1) - S.ut x‖ ≤
        Cb * (c0 * (L : ℝ) ^ j₀ / d) ^ (-1 - (d : ℝ) / 2) *
          Real.sqrt (∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * (c0 * (L : ℝ) ^ j₀ / d)),
            ‖S.ut (liftPt x w)‖ ^ 2) +
        ∑ z ∈ latticeBall (0 : Fin d → ℤ) (2 * (c0 * (L : ℝ) ^ j₀ / d)),
          |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| *
            ‖negLap (fun w => S.ut (liftPt x w)) z‖)
    (hG : ∀ R : ℝ, 0 ≤ R → ∀ A : Finset (Fin d → ℤ),
      A.card ≤ (latticeBall (0 : Fin d → ℤ) R).card →
      (∑ z ∈ A, latticeGreen d (0 - z) ≤ cG * (R + 1) ^ 2) ∧
      (∀ ν : Fin d, ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| ≤
        cG * (R + 1))) :
    S.U x ≤ ((Ca + d * (d * L / c0) * Cb) *
        (2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) * (L : ℝ) ^ 2 * bd d L ^ 2 /
          Real.sqrt ((c0 / d) ^ d)) +
        cG * (4 + 2 * d * L) * Real.exp (agmonRate d / 2 * (2 * d + 1))) *
        Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf) +
      cG * (36 + 12 * L) * c0 * M := by
  have hc := poincareConst_pos S.hd0
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast S.hd0
  have hd0 : (0 : ℝ) < d := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hLc : (0 : ℝ) < (L : ℝ) ^ j₀ := by positivity
  have hj2 : 2 ≤ j₀ + 1 := by omega
  set ρ := c0 * (L : ℝ) ^ j₀ / d with hρdef
  have hρ0 : 0 < ρ := by linarith
  have hRd : (d : ℝ) * (2 * ρ) ≤ (L : ℝ) ^ j₀ := by
    rw [hρdef]; field_simp; nlinarith
  set ball := latticeBall (0 : Fin d → ℤ) (2 * ρ) with hball
  have hzb : ∀ z ∈ ball, (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (j₀ + 1 - 1) := by
    intro z hz
    have := (mem_latticeBall (by positivity)).1 hz
    rw [sub_zero] at this
    simp only [Nat.add_sub_cancel]
    exact (mul_le_mul_of_nonneg_left this (Nat.cast_nonneg d)).trans hRd
  set m := 4 * (((L : ℝ) ^ j₀) ^ 2)⁻¹ * M with hm
  have hm0 : 0 ≤ m := by positivity
  have hM' : ∀ q ∈ G.Ω 1, G.pathDist q x ≤ ENNReal.ofReal (2 * d + 1) → ‖S.ut q‖ ≤ M :=
    fun q hq h => (S.norm_ut_le_U q).trans (hM q hq h)
  have hg : ∀ z ∈ ball, ‖negLap (fun w => S.ut (liftPt x w)) z‖ ≤ ‖S.ft (liftPt x z)‖ + m := by
    intro z hz
    have := S.g_bound hj2 hjk hx (hzb z hz) hM0 hM'
    simpa only [Nat.add_sub_cancel] using this
  have hT := S.l2_part hc0 hc04 hj2 hjk hx (by simpa using hρ) hMf0 hMf ht0 ht
  simp only [Nat.add_sub_cancel] at hT
  set Tval := ρ ^ (-(d : ℝ) / 2) *
    Real.sqrt (∑ w ∈ ball, ‖S.ut (liftPt x w)‖ ^ 2) with hTval
  obtain ⟨A, hzero, hftot⟩ := S.case2_fpart hcG hc0 hc04 hj01 hjk hx hMf0 hMf ht hG hρ0 hRd
  obtain ⟨hGB, hGBν⟩ := hG (2 * ρ) (by positivity) ball le_rfl
  have hCnn : ∀ z : Fin d → ℤ, 0 ≤ latticeGreen d (0 - z) := fun z => latticeGreen_nonneg _
  have hSa : ∑ z ∈ ball, latticeGreen d (0 - z) * ‖negLap (fun w => S.ut (liftPt x w)) z‖ ≤
      Mf * ∑ z ∈ A, latticeGreen d (0 - z) + m * (cG * (2 * ρ + 1) ^ 2) := by
    calc _ ≤ ∑ z ∈ ball, latticeGreen d (0 - z) * (‖S.ft (liftPt x z)‖ + m) :=
          Finset.sum_le_sum fun z hz =>
            mul_le_mul_of_nonneg_left (hg z hz) (latticeGreen_nonneg _)
      _ = ∑ z ∈ ball, latticeGreen d (0 - z) * ‖S.ft (liftPt x z)‖ +
          m * ∑ z ∈ ball, latticeGreen d (0 - z) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ ≤ _ := add_le_add (hzero _ hCnn) (mul_le_mul_of_nonneg_left hGB hm0)
  have hSb : ∀ ν : Fin d, ∑ z ∈ ball, |latticeGreen d (0 - z + Pi.single ν 1) -
        latticeGreen d (0 - z)| * ‖negLap (fun w => S.ut (liftPt x w)) z‖ ≤
      Mf * ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| +
        m * (cG * (2 * ρ + 1)) := by
    intro ν
    calc _ ≤ ∑ z ∈ ball, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| *
          (‖S.ft (liftPt x z)‖ + m) :=
          Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hg z hz) (abs_nonneg _)
      _ = ∑ z ∈ ball, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| *
            ‖S.ft (liftPt x z)‖ + m * ∑ z ∈ ball, |latticeGreen d (0 - z + Pi.single ν 1) -
              latticeGreen d (0 - z)| := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ ≤ _ := add_le_add (hzero (fun z => |latticeGreen d (0 - z + Pi.single ν 1) -
            latticeGreen d (0 - z)|) (fun z => abs_nonneg _))
            (mul_le_mul_of_nonneg_left (hGBν ν) hm0)
  have hsp : G.spacing x = (L : ℝ) ^ (j₀ + 1) := G.spacing_eq (by omega) hjk hx
  have hsp0 : 0 < (L : ℝ) ^ (j₀ + 1) := by positivity
  have hUa : ‖S.ut x‖ ≤ Ca * Tval + (Mf * ∑ z ∈ A, latticeGreen d (0 - z) +
      m * (cG * (2 * ρ + 1) ^ 2)) := by
    have e : Ca * ρ ^ (-(d : ℝ) / 2) * Real.sqrt (∑ w ∈ ball, ‖S.ut (liftPt x w)‖ ^ 2) =
        Ca * Tval := by rw [hTval]; ring
    linarith only [hLa, hSa, e]
  have hUb : ∀ ν : Fin d, ‖S.ut (x + Pi.single ν 1) - S.ut x‖ ≤ Cb * ρ⁻¹ * Tval +
      (Mf * ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| +
        m * (cG * (2 * ρ + 1))) := by
    intro ν
    have e : Cb * ρ ^ (-1 - (d : ℝ) / 2) * Real.sqrt (∑ w ∈ ball, ‖S.ut (liftPt x w)‖ ^ 2) =
        Cb * ρ⁻¹ * Tval := by
      rw [hTval, rpow_neg_one_sub_half hρ0 d]; ring
    linarith only [hLb ν, hSb ν, e]
  have hsumΔ : ∑ ν : Fin d, ‖S.ut (x + Pi.single ν 1) - S.ut x‖ ≤
      d * (Cb * ρ⁻¹ * Tval) + ∑ ν : Fin d, (Mf * ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) -
        latticeGreen d (0 - z)|) + d * (m * (cG * (2 * ρ + 1))) := by
    calc _ ≤ ∑ ν : Fin d, (Cb * ρ⁻¹ * Tval + (Mf * ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) -
          latticeGreen d (0 - z)| + m * (cG * (2 * ρ + 1)))) := Finset.sum_le_sum fun ν _ => hUb ν
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp
          ring
  have hsr : (L : ℝ) ^ (j₀ + 1) * ρ⁻¹ = d * L / c0 := by
    rw [hρdef]; field_simp; ring
  have hpot := pot_arith (cG := cG) (c0 := c0) (L := (L : ℝ)) (d := (d : ℝ)) (M := M)
    (Lc := (L : ℝ) ^ j₀) hcG hc0 (by linarith) hL1 hd1 hLc hM0 (by linarith)
  have hX1 : 0 ≤ Ca + d * (d * L / c0) * Cb := by positivity
  have hT' := mul_le_mul_of_nonneg_left hT hX1
  have hU : S.U x ≤ ‖S.ut x‖ + (L : ℝ) ^ (j₀ + 1) * ∑ ν : Fin d, ‖S.ut (x + Pi.single ν 1) - S.ut x‖ := by
    unfold PtSetting.U
    rw [hsp]
  have hU2 := mul_le_mul_of_nonneg_left hsumΔ hsp0.le
  have hpow : (L : ℝ) ^ (j₀ + 1) = (L : ℝ) ^ j₀ * L := pow_succ _ _
  have key : (Ca * Tval + (Mf * ∑ z ∈ A, latticeGreen d (0 - z) + m * (cG * (2 * ρ + 1) ^ 2))) +
      (L : ℝ) ^ (j₀ + 1) * (d * (Cb * ρ⁻¹ * Tval) + ∑ ν : Fin d, (Mf * ∑ z ∈ A,
        |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)|) +
        d * (m * (cG * (2 * ρ + 1)))) =
      (Ca + d * (d * L / c0) * Cb) * Tval +
      (Mf * ∑ z ∈ A, latticeGreen d (0 - z) + (L : ℝ) ^ (j₀ + 1) * ∑ ν : Fin d, (Mf * ∑ z ∈ A,
        |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)|)) +
      (m * (cG * (2 * ρ + 1) ^ 2) + ((L : ℝ) ^ j₀ * L) * d * (m * (cG * (2 * ρ + 1)))) := by
    rw [← hpow]
    linear_combination (d * Cb * Tval) * hsr
  have hfin : S.U x ≤ (Ca + d * (d * L / c0) * Cb) * Tval +
      (Mf * ∑ z ∈ A, latticeGreen d (0 - z) + (L : ℝ) ^ (j₀ + 1) * ∑ ν : Fin d, (Mf * ∑ z ∈ A,
        |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)|)) +
      (m * (cG * (2 * ρ + 1) ^ 2) + ((L : ℝ) ^ j₀ * L) * d * (m * (cG * (2 * ρ + 1)))) := by
    rw [← key]
    linarith only [hU, hUa, hU2]
  have hmain : (Ca + d * (d * L / c0) * Cb) * Tval ≤ (Ca + d * (d * L / c0) * Cb) *
      (2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) * (L : ℝ) ^ 2 * bd d L ^ 2 /
        Real.sqrt ((c0 / d) ^ d) * Real.exp (-(agmonRate d / 2 * t)) *
        ((L : ℝ) ^ (2 * S.j') * Mf)) := hT'
  have hfin2 : (Ca + d * (d * L / c0) * Cb) * (2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) *
        (L : ℝ) ^ 2 * bd d L ^ 2 / Real.sqrt ((c0 / d) ^ d) * Real.exp (-(agmonRate d / 2 * t)) *
        ((L : ℝ) ^ (2 * S.j') * Mf)) =
      (Ca + d * (d * L / c0) * Cb) * (2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) *
        (L : ℝ) ^ 2 * bd d L ^ 2 / Real.sqrt ((c0 / d) ^ d)) * Real.exp (-(agmonRate d / 2 * t)) *
        ((L : ℝ) ^ (2 * S.j') * Mf) := by ring
  have hexp : ((Ca + d * (d * L / c0) * Cb) *
        (2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) * (L : ℝ) ^ 2 * bd d L ^ 2 /
          Real.sqrt ((c0 / d) ^ d)) +
        cG * (4 + 2 * d * L) * Real.exp (agmonRate d / 2 * (2 * d + 1))) *
        Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf) =
      (Ca + d * (d * L / c0) * Cb) * (2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) *
        (L : ℝ) ^ 2 * bd d L ^ 2 / Real.sqrt ((c0 / d) ^ d)) * Real.exp (-(agmonRate d / 2 * t)) *
        ((L : ℝ) ^ (2 * S.j') * Mf) +
      cG * (4 + 2 * d * L) * Real.exp (agmonRate d / 2 * (2 * d + 1)) *
        Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf) := by ring
  rw [hexp]
  linarith only [hfin, hmain, hfin2, hftot, hpot]

end PtSetting

end Balaban.Multiscale
