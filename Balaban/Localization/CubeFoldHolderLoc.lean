/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CutLemmaPCube
public import Balaban.Localization.CubeFoldSource
public import Balaban.Localization.CutPointwiseWallBall
public import Balaban.Multiscale.PointwiseHolderI
public import Balaban.Multiscale.PointwiseCase2d
public import Balaban.Green.Lattice.LocHolder
public import Balaban.Green.Lattice.HolderSums

/-!
# The folded Lemma Loc (c) for the cut solution (VMOD-10 §3, (3.3)--(3.11))

`locCc`, `locCH`: chosen constants of `lemma_loc_c` and `green_holder_sum`; `holderKs`: the short-regime
constant. `cubeFold_holder_pre`: the decomposition of the folded Loc (c) bound into the `ℓ²` part, the
source part and the potential part. `cubeFold_holder_fold`: the folded Hölder estimate (before the
pointwise decay is inserted),
`ℓ² |Δ| ≤ (K_s/θ) ℓ^θ r^{1-θ} (e^{-γ t} L^{2j'} M_f + M)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.LatticeGreen Balaban.Reflection Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The constant `C_c(d)` of the landed `lemma_loc_c` (chosen). -/
noncomputable def locCc (d : ℕ) : ℝ :=
  if h : 3 ≤ d then Classical.choose (lemma_loc_c h) else 0

/-- The constant `c_H(d)` of the landed `green_holder_sum` (chosen). -/
noncomputable def locCH (d : ℕ) : ℝ :=
  if h : 3 ≤ d then Classical.choose (green_holder_sum h) else 0

theorem locCc_spec (hd : 3 ≤ d) : 0 ≤ locCc d ∧ ∀ (ρ : ℝ), 8 ≤ ρ → ∀ (x₀ x x' : Fin d → ℤ),
    ‖x - x₀‖ ≤ ρ / 2 → ‖x' - x₀‖ ≤ ρ / 2 → ∀ (r : ℝ), ‖x - x'‖ ≤ r → r ≤ ρ / 4 →
      ∀ (ν : Fin d) (u g : (Fin d → ℤ) → ℂ),
        (∀ z, ‖z - x₀‖ ≤ 2 * ρ - 1 → negLap u z = g z) →
        ‖(u (x + Pi.single ν 1) - u x) - (u (x' + Pi.single ν 1) - u x')‖ ≤
          locCc d * r * ρ ^ (-2 - (d : ℝ) / 2) *
            Real.sqrt (∑ w ∈ latticeBall x₀ (2 * ρ), ‖u w‖ ^ 2) +
          ∑ z ∈ latticeBall x₀ (2 * ρ), |greenDiff d ν (x - z) - greenDiff d ν (x' - z)| *
            ‖g z‖ := by
  unfold locCc
  simp only [hd, ↓reduceDIte]
  exact Classical.choose_spec (lemma_loc_c hd)

theorem locCH_spec (hd : 3 ≤ d) : 0 ≤ locCH d ∧ ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ {r : ℝ}, 1 ≤ r →
    ∀ (a : Fin d → ℤ), ‖a‖ ≤ r → ∀ (ν : Fin d) {R : ℝ}, 0 ≤ R → ∀ (A : Finset (Fin d → ℤ)),
      A.card ≤ (latticeBall (0 : Fin d → ℤ) R).card → ∀ y0 : Fin d → ℤ,
      ∑ z ∈ A, |greenDiff d ν (y0 - z + a) - greenDiff d ν (y0 - z)| ≤
        locCH d / θ * (r + r ^ (1 - θ) * (R + 1) ^ θ) := by
  unfold locCH
  simp only [hd, ↓reduceDIte]
  exact Classical.choose_spec (green_holder_sum hd)

/-- **The constant `K_short`-type bound of VMOD-10 (1.3)** (before the pointwise decay is inserted):
`C_c κ² 2^{d/2} C₂ + 3 L² c_H e^{γ D₀} + 16 L² c_H`, `κ = dL/c₀`. -/
noncomputable def holderKs (d L : ℕ) : ℝ :=
  locCc d * (d * L / cutC0 d L) ^ 2 * (Real.sqrt (2 ^ d) * holderKl2 d L (cutC0 d L)) +
    3 * (L : ℝ) ^ 2 * locCH d * Real.exp (agmonRate d / 2 * (2 * d + 1)) +
    16 * (L : ℝ) ^ 2 * locCH d

omit [NeZero L] in
theorem holderKs_nonneg (hd : 3 ≤ d) : 0 ≤ holderKs d L := by
  have hCc := (locCc_spec hd).1
  have hcH := (locCH_spec hd).1
  have := holderKl2_nonneg d L (cutC0 d L)
  unfold holderKs
  positivity

/-- **The decomposition of the folded Loc (c) bound** (VMOD-10 (3.3)--(3.7)). -/
theorem cubeFold_holder_pre (hd : 3 ≤ d) (hL : 3 ≤ L) {G : GeneratingSet d L N₀ k ϱ}
    (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (hSℓ : S < N₀ * L ^ k)
    {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α *ᵥ u = f)
    (hΛ : BlockAligned G (cubeSet (N₀ * L ^ k) S c))
    {j₀ j' : ℕ} (hj01 : 1 ≤ j₀) (hjk : j₀ + 1 ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {x y' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer (j₀ + 1)) (hy' : y' ∈ G.layer j')
    (hxΛ : x ∈ cubeSet (N₀ * L ^ k) S c)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    (hρ : 8 ≤ cutC0 d L * (L : ℝ) ^ j₀ / d) {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖f i‖ ≤ Mf)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist x y') {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ G.Ω 1, G.pathDist z x ≤ ENNReal.ofReal (2 * d + 1) →
      cutU G (cubeCut G (cubeSet (N₀ * L ^ k) S c)) (zeroExt (G.Ω 1) u) z ≤ M)
    (p0 : Torus d (2 * S)) (hp0 : foldMap (N₀ * L ^ k) S (2 * S) c p0 = x)
    {z : Fin d → ℤ} (hz1 : 1 ≤ ‖z‖) (hzρ : ‖z‖ ≤ (cutC0 d L * (L : ℝ) ^ j₀ / d) / 4)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (μ : Fin d) :
    ∃ Tv SA Sb : ℝ,
      ‖(zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 (z + Pi.single μ 1)) -
            zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 z)) -
          (zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 (Pi.single μ 1)) -
            zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 0))‖ ≤
        locCc d * ‖z‖ * ((cutC0 d L * (L : ℝ) ^ j₀ / d) ^ 2)⁻¹ * Tv +
          (Mf * SA + 4 * (((L : ℝ) ^ j₀) ^ 2)⁻¹ * M * Sb) ∧
      Tv ≤ (Real.sqrt (2 ^ d) * holderKl2 d L (cutC0 d L)) * Real.exp (-(agmonRate d / 2 * t)) *
        ((L : ℝ) ^ (2 * j') * Mf) ∧
      SA ≤ locCH d / θ * (‖z‖ + ‖z‖ ^ (1 - θ) * ((((L ^ j' : ℕ)) : ℝ) + 1) ^ θ) ∧
      Sb ≤ locCH d / θ * (‖z‖ + ‖z‖ ^ (1 - θ) * (2 * (cutC0 d L * (L : ℝ) ^ j₀ / d) + 1) ^ θ) ∧
      (SA = 0 ∨ ((L : ℝ) ^ (j₀ + 1) ≤ L * (L : ℝ) ^ j' ∧
        1 ≤ Real.exp (agmonRate d / 2 * (2 * d + 1)) * Real.exp (-(agmonRate d / 2 * t)))) := by
  have hd0 : 0 < d := by omega
  have hc := poincareConst_pos hd0
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hd0' : (0 : ℝ) < d := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hLc0 : (0 : ℝ) < (L : ℝ) ^ j₀ := by positivity
  have hj2 : 2 ≤ j₀ + 1 := by omega
  obtain ⟨hCc, hLcloc⟩ := locCc_spec hd
  obtain ⟨hcH, hHs⟩ := locCH_spec hd
  have hc0 := cutC0_pos (L := L) hd
  have hc04 := cutC0_le (d := d) (L := L)
  have hS : L ^ (j₀ + 1) ≤ S :=
    side_ge_of_blockAligned G hd0 hΛ (by omega) hjk hx hxΛ
  obtain ⟨hRd, hRd1, hdL, hρle⟩ := case2_radius_arith hd1 hc0 hc04 hLc0 hρ
  set c0 := cutC0 d L with hc0def
  set ρ := c0 * (L : ℝ) ^ j₀ / d with hρdef
  have hρ0 : 0 < ρ := by linarith
  have hRS : 2 * ρ < S := by
    have h2 : (L : ℝ) ^ (j₀ + 1) ≤ S := by exact_mod_cast hS
    have h3 : (L : ℝ) ^ j₀ < (L : ℝ) ^ (j₀ + 1) := by
      rw [pow_succ]
      have : (3 : ℝ) ≤ L := by exact_mod_cast hL
      nlinarith
    have h4 : 2 * ρ ≤ (L : ℝ) ^ j₀ :=
      (le_mul_of_one_le_left (by positivity) hd1).trans hRd
    linarith
  set ball := latticeBall (0 : Fin d → ℤ) (2 * ρ) with hball
  set ut := zeroExt (G.Ω 1) u with hut
  set ft := zeroExt (G.Ω 1) f with hft
  set P := cubeFoldPt N₀ L k S c p0 with hP
  have hzb : ∀ w ∈ ball, (d : ℝ) * (‖w‖ + 1) ≤ (L : ℝ) ^ (j₀ + 1 - 1) := by
    intro w hw
    have := (mem_latticeBall (by positivity)).1 hw
    rw [sub_zero] at this
    simp only [Nat.add_sub_cancel]
    exact (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg d)).trans hRd1
  set m := (3 + 1) * (((L : ℝ) ^ j₀) ^ 2)⁻¹ * M with hm
  have hm0 : 0 ≤ m := by positivity
  have hg : ∀ w ∈ ball, ‖negLap (fun w => ut (P w)) w‖ ≤ ‖ft (P w)‖ + m := by
    intro w hw
    have := cubeFold_local_poisson_bound G hϱ hν hν1 ha S c hSℓ hu (j := j₀ + 1) hj2 hjk hx p0 hp0
      (hzb w hw) hM0 hα hM
    simpa only [Nat.add_sub_cancel] using this
  have hcut : CutAligned G (cubeCut G (cubeSet (N₀ * L ^ k) S c)) := cubeCut_aligned G hΛ
  have hT := cubeFold_ball_l2 hcut hd hL hϱ hsep hν ha α hα hu hj01 hjk hj'1 hj'k hx hy' hsupp S c
    p0 hp0 hSℓ hS hc0 hc04 hρ hMf0 hMf ht0 ht
  set Tv := ρ ^ (-(d : ℝ) / 2) * Real.sqrt (∑ w ∈ ball, ‖ut (P w)‖ ^ 2) with hTv
  obtain ⟨A, hAsub, hAcard, hAvan, hAne⟩ := cubeFold_fsum_data hd hL hϱ hsep hj2 hjk hj'1 hj'k hx
    hy' hsupp S c p0 hp0 hSℓ (R := 2 * ρ) (by positivity)
    (by simpa only [Nat.add_sub_cancel] using hRd) hRS
  set r := ‖z‖ with hrdef
  have hr0 : 0 < r := by linarith
  set Kf : (Fin d → ℤ) → ℝ := fun w =>
    |greenDiff d μ (0 - w + z) - greenDiff d μ (0 - w)| with hKf
  have hKf0 : ∀ w, 0 ≤ Kf w := fun w => abs_nonneg _
  have hKeq : ∀ w, |greenDiff d μ (z - w) - greenDiff d μ (0 - w)| = Kf w := by
    intro w
    simp only [hKf]
    have : z - w = 0 - w + z := by abel
    rw [this]
  have hSb : ∑ w ∈ ball, Kf w ≤ locCH d / θ * (r + r ^ (1 - θ) * (2 * ρ + 1) ^ θ) :=
    hHs hθ0 hθ1 hz1 z le_rfl μ (by positivity) ball le_rfl 0
  set Rf : ℝ := (((L ^ j' : ℕ)) : ℝ) with hRf
  have hRf0 : 0 ≤ Rf := Nat.cast_nonneg _
  have hAcard' : A.card ≤ (latticeBall (0 : Fin d → ℤ) Rf).card := by
    rw [hRf, card_latticeBall_nat]
    refine hAcard.trans ?_
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) d
  have hSA : ∑ w ∈ A, Kf w ≤ locCH d / θ * (r + r ^ (1 - θ) * (Rf + 1) ^ θ) :=
    hHs hθ0 hθ1 hz1 z le_rfl μ hRf0 A hAcard' 0
  have hnorm : ∀ p : Torus d (N₀ * L ^ k), ‖ft p‖ ≤ Mf := by
    intro p
    simp only [hft]
    unfold zeroExt
    split_ifs with h
    · exact hMf _
    · simpa using hMf0
  have hsplit : ∑ w ∈ ball, Kf w * ‖negLap (fun w => ut (P w)) w‖ ≤
      Mf * ∑ w ∈ A, Kf w + m * ∑ w ∈ ball, Kf w := by
    calc _ ≤ ∑ w ∈ ball, Kf w * (‖ft (P w)‖ + m) :=
          Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left (hg w hw) (hKf0 w)
      _ = ∑ w ∈ ball, Kf w * ‖ft (P w)‖ + m * ∑ w ∈ ball, Kf w := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun w _ => by ring
      _ ≤ _ := by
          refine add_le_add ?_ le_rfl
          have h1 : ∑ w ∈ ball, Kf w * ‖ft (P w)‖ = ∑ w ∈ A, Kf w * ‖ft (P w)‖ :=
            (Finset.sum_subset hAsub (fun w hw hnA => by
              have h := hAvan w hw hnA
              change ft (P w) = 0 at h
              rw [h]; simp)).symm
          rw [h1, Finset.mul_sum]
          refine Finset.sum_le_sum fun w _ => ?_
          rw [mul_comm Mf]
          exact mul_le_mul_of_nonneg_left (hnorm _) (hKf0 w)
  have hLc := hLcloc ρ hρ 0 z 0 (by simp only [sub_zero]; linarith)
    (by simp only [sub_self, norm_zero]; linarith) r (by simp [hrdef]) hzρ μ
    (fun w => ut (P w)) (fun w => negLap (fun w => ut (P w)) w) (fun z _ => rfl)
  simp only [zero_add] at hLc
  have hmain : ‖(ut (P (z + Pi.single μ 1)) - ut (P z)) - (ut (P (Pi.single μ 1)) - ut (P 0))‖ ≤
      locCc d * r * (ρ ^ 2)⁻¹ * Tv + (Mf * ∑ w ∈ A, Kf w + m * ∑ w ∈ ball, Kf w) := by
    have e1 : locCc d * r * ρ ^ (-2 - (d : ℝ) / 2) *
        Real.sqrt (∑ w ∈ ball, ‖ut (P w)‖ ^ 2) = locCc d * r * (ρ ^ 2)⁻¹ * Tv := by
      rw [rpow_neg_two_sub_half hρ0 d, hTv]; ring
    have e2 : ∑ w ∈ ball, |greenDiff d μ (z - w) - greenDiff d μ (0 - w)| *
        ‖negLap (fun w => ut (P w)) w‖ =
        ∑ w ∈ ball, Kf w * ‖negLap (fun w => ut (P w)) w‖ :=
      Finset.sum_congr rfl fun w _ => by rw [hKeq]
    rw [e1, e2] at hLc
    have h3 := add_le_add (le_refl (locCc d * r * (ρ ^ 2)⁻¹ * Tv)) hsplit
    exact hLc.trans h3
  have hTv' : Tv ≤ (Real.sqrt (2 ^ d) * holderKl2 d L c0) * Real.exp (-(agmonRate d / 2 * t)) *
      ((L : ℝ) ^ (2 * j') * Mf) := by
    refine hT.trans (le_of_eq ?_)
    unfold holderKl2
    ring
  have hℓeq : (L : ℝ) ^ (j₀ + 1) = L * (L : ℝ) ^ j₀ := by rw [pow_succ']
  have hsrc : ∑ w ∈ A, Kf w = 0 ∨ ((L : ℝ) ^ (j₀ + 1) ≤ L * (L : ℝ) ^ j' ∧
      1 ≤ Real.exp (agmonRate d / 2 * (2 * d + 1)) * Real.exp (-(agmonRate d / 2 * t))) := by
    by_cases hAn : A.Nonempty
    · obtain ⟨hpd, hjj⟩ := hAne hAn
      right
      have hε0 := agmonRate_pos hd0
      have ht_le : t ≤ 2 * d + 1 := by
        have := ht.trans hpd
        rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
      refine ⟨?_, ?_⟩
      · rw [hℓeq]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by omega)) hL0.le
      · rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith only [ht_le, hε0]
    · left
      rw [Finset.not_nonempty_iff_eq_empty.1 hAn]
      simp
  have e4 : (3 + 1 : ℝ) = 4 := by norm_num
  rw [hm, e4] at hmain
  exact ⟨Tv, ∑ w ∈ A, Kf w, ∑ w ∈ ball, Kf w, hmain, hTv', hSA, hSb, hsrc⟩

/-- **The folded Hölder estimate in the short regime** (VMOD-10 (3.6)--(3.11), before decay). -/
theorem cubeFold_holder_fold (hd : 3 ≤ d) (hL : 3 ≤ L) {G : GeneratingSet d L N₀ k ϱ}
    (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (hSℓ : S < N₀ * L ^ k)
    {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α *ᵥ u = f)
    (hΛ : BlockAligned G (cubeSet (N₀ * L ^ k) S c))
    {j₀ j' : ℕ} (hj01 : 1 ≤ j₀) (hjk : j₀ + 1 ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {x y' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer (j₀ + 1)) (hy' : y' ∈ G.layer j')
    (hxΛ : x ∈ cubeSet (N₀ * L ^ k) S c)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    (hρ : 8 ≤ cutC0 d L * (L : ℝ) ^ j₀ / d) {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖f i‖ ≤ Mf)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist x y') {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ G.Ω 1, G.pathDist z x ≤ ENNReal.ofReal (2 * d + 1) →
      cutU G (cubeCut G (cubeSet (N₀ * L ^ k) S c)) (zeroExt (G.Ω 1) u) z ≤ M)
    (p0 : Torus d (2 * S)) (hp0 : foldMap (N₀ * L ^ k) S (2 * S) c p0 = x)
    {z : Fin d → ℤ} (hz1 : 1 ≤ ‖z‖) (hzρ : ‖z‖ ≤ (cutC0 d L * (L : ℝ) ^ j₀ / d) / 4)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (μ : Fin d) :
    ((L : ℝ) ^ (j₀ + 1)) ^ 2 *
        ‖(zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 (z + Pi.single μ 1)) -
            zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 z)) -
          (zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 (Pi.single μ 1)) -
            zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 0))‖ ≤
      (holderKs d L / θ) * (((L : ℝ) ^ (j₀ + 1)) ^ θ * ‖z‖ ^ (1 - θ)) *
        (Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * j') * Mf) + M) := by
  obtain ⟨Tv, SA, Sb, hmain, hTv, hSA, hSb, hsrc⟩ := cubeFold_holder_pre hd hL hϱ hsep hν hν1 ha α hα
    S c hSℓ hu hΛ hj01 hjk hj'1 hj'k hx hy' hxΛ hsupp hρ hMf0 hMf ht0 ht hM0 hM p0 hp0 hz1 hzρ
    hθ0 hθ1 μ
  obtain ⟨hCc, -⟩ := locCc_spec hd
  obtain ⟨hcH, -⟩ := locCH_spec hd
  have hc0 := cutC0_pos (L := L) hd
  have hc04 := cutC0_le (d := d) (L := L)
  have hd0 : 0 < d := by omega
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hd0' : (0 : ℝ) < d := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hLc0 : (0 : ℝ) < (L : ℝ) ^ j₀ := by positivity
  have hρ0 : 0 < cutC0 d L * (L : ℝ) ^ j₀ / d := by positivity
  have hr0 : 0 < ‖z‖ := by linarith
  have hLj'1 : (1 : ℝ) ≤ (L : ℝ) ^ j' := one_le_pow₀ hL1
  have hRf1 : (((L ^ j' : ℕ)) : ℝ) + 1 ≤ 2 * (L : ℝ) ^ j' := by push_cast; linarith
  have hℓeq : (L : ℝ) ^ (j₀ + 1) = L * (L : ℝ) ^ j₀ := by rw [pow_succ']
  have hρL : cutC0 d L * (L : ℝ) ^ j₀ / d ≤ (L : ℝ) ^ j₀ := by
    rw [div_le_iff₀ hd0']
    nlinarith only [hc04, hLc0, hd1]
  have hρℓ : cutC0 d L * (L : ℝ) ^ j₀ / d ≤ (L : ℝ) ^ (j₀ + 1) := by
    rw [hℓeq]; exact hρL.trans (le_mul_of_one_le_left hLc0.le hL1)
  have hκ : (L : ℝ) ^ (j₀ + 1) = (d * L / cutC0 d L) * (cutC0 d L * (L : ℝ) ^ j₀ / d) := by
    rw [hℓeq]; field_simp
  have h1 := holder_assemble (Dn := ‖(zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 (z + Pi.single μ 1)) -
            zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 z)) -
          (zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 (Pi.single μ 1)) -
            zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 0))‖) (Tv := Tv) (SA := SA) (Sb := Sb)
    (F := (L : ℝ) ^ (2 * j') * Mf) (m := 4 * (((L : ℝ) ^ j₀) ^ 2)⁻¹ * M) (Cc := locCc d)
    (cH := locCH d) (θ := θ) (r := ‖z‖) (ρ := cutC0 d L * (L : ℝ) ^ j₀ / d)
    (ℓ := (L : ℝ) ^ (j₀ + 1)) (κ := d * L / cutC0 d L)
    (Kl2 := Real.sqrt (2 ^ d) * holderKl2 d L (cutC0 d L))
    (e := Real.exp (-(agmonRate d / 2 * t))) (E1 := Real.exp (agmonRate d / 2 * (2 * d + 1)))
    (L := (L : ℝ)) (Lj := (L : ℝ) ^ j₀) (Lj' := (L : ℝ) ^ j') (Rf := (((L ^ j' : ℕ)) : ℝ))
    hCc hcH hθ0 hθ1.le hr0 (by linarith) hρℓ (by linarith) hκ hℓeq hL0 hL1 hLc0 hLj'1 hMf0 hM0 rfl
    (Real.exp_pos _) (by rw [pow_mul']) (by have := holderKl2_nonneg d L (cutC0 d L); positivity)
    (Real.exp_pos _).le hmain hTv hSA hRf1 (Nat.cast_nonneg _) hSb hsrc
  refine h1.trans ?_
  have hX' : 0 ≤ ((L : ℝ) ^ (j₀ + 1)) ^ θ * ‖z‖ ^ (1 - θ) := by positivity
  have hEF : 0 ≤ Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * j') * Mf) := by positivity
  have hq := holderKl2_nonneg d L (cutC0 d L)
  have hE1 := (Real.exp_pos (agmonRate d / 2 * (2 * d + 1))).le
  refine holder_final_I (B := holderKs d L) ?_ ?_ hθ0 hX' hEF hM0
  · unfold holderKs
    have : 0 ≤ 16 * (L : ℝ) ^ 2 * locCH d := by positivity
    have h5 : 0 ≤ locCc d * (d * L / cutC0 d L) ^ 2 * (Real.sqrt (2 ^ d) * holderKl2 d L (cutC0 d L)) := by
      positivity
    have h6 : 0 ≤ 3 * (L : ℝ) ^ 2 * locCH d * Real.exp (agmonRate d / 2 * (2 * d + 1)) := by
      positivity
    linarith only [h5, h6, this]
  · unfold holderKs
    have h5 : 0 ≤ locCc d * (d * L / cutC0 d L) ^ 2 * (Real.sqrt (2 ^ d) * holderKl2 d L (cutC0 d L)) := by
      positivity
    have h6 : 0 ≤ 3 * (L : ℝ) ^ 2 * locCH d * Real.exp (agmonRate d / 2 * (2 * d + 1)) := by
      positivity
    linarith only [h5, h6]

end Balaban.Localization
