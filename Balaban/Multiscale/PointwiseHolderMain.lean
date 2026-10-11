/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseHolder

/-!
# Proposition 4.9 (G-2(iii)): the Hölder bound for the gradient

* `holder_bound` (the Hölder analogue of Lemma P, without recursion): for a Hölder pair
  `(x, x + z)` and every `0 ≤ t ≤ d(x, y')`,
  `ℓ(x)² |∂u(x + z) - ∂u(x)| ≤ (B/θ) ℓ(x)^θ ‖z‖^{1-θ} (e^{-(ε₀/2) t} ℓ_{j'}² ‖f‖_∞ + M)`
  with `M` a bound of `U` on the `(2d+1)`-neighbourhood of `x`, and `B = B(d, L)` independent of `θ`;
* `prop49`: with `M` from Proposition 4.8,
  `ℓ(x)^{2-θ} ‖z‖^{-(1-θ)} |∂u(x + z) - ∂u(x)| ≤ (B_θ) e^{-(ε₀/2) d(x, y')} ℓ_{j'}² ‖f‖_∞`,
  `B_θ = C(d, L)/θ`, and `∂u(x + z) = ∂u(x)` if `d(x, y') = ∞`.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban Balaban.LatticeGreen

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The constant `B` of `holder_bound`. -/
def holderConst (d L : ℕ) (Cc cH : ℝ) : ℝ :=
  Cc * (d * L / (1 / 4 : ℝ)) ^ 2 * holderKl2 d L (1 / 4) +
    3 * (L : ℝ) ^ 2 * cH * Real.exp (agmonRate d / 2 * (2 * d + 1)) +
    16 * (L : ℝ) ^ 2 * cH + (L + 1) * (32 * d * L)

omit [NeZero L] in
theorem holderConst_nonneg {Cc cH : ℝ} (hCc : 0 ≤ Cc) (hcH : 0 ≤ cH) :
    0 ≤ holderConst d L Cc cH := by
  unfold holderConst
  have := holderKl2_nonneg d L (1 / 4)
  positivity

/-- The case split: `ℓ ≤ K` or `ℓ ≤ K ‖z‖` outside the Loc (c) regime. -/
theorem holder_scale_cases {j : ℕ} (hj : 1 ≤ j) {r : ℝ}
    (hnot : ¬ (2 ≤ j ∧ 8 ≤ (1 / 4 : ℝ) * (L : ℝ) ^ (j - 1) / d ∧
      r ≤ ((1 / 4 : ℝ) * (L : ℝ) ^ (j - 1) / d) / 4)) (hd : 1 ≤ d) :
    (L : ℝ) ^ j ≤ 32 * d * L ∨ (L : ℝ) ^ j ≤ 32 * d * L * r := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hpow : (L : ℝ) ^ j = L * (L : ℝ) ^ (j - 1) := by
    rw [← pow_succ']; congr 1; omega
  by_cases hj2 : 2 ≤ j
  · by_cases h8 : 8 ≤ (1 / 4 : ℝ) * (L : ℝ) ^ (j - 1) / d
    · right
      have hr : ((1 / 4 : ℝ) * (L : ℝ) ^ (j - 1) / d) / 4 < r := by
        by_contra hcon
        exact hnot ⟨hj2, h8, not_lt.1 hcon⟩
      have e : (L : ℝ) ^ (j - 1) = 4 * d * ((1 / 4 : ℝ) * (L : ℝ) ^ (j - 1) / d) := by
        field_simp
      rw [hpow, e]
      have hρ0 : 0 < (1 / 4 : ℝ) * (L : ℝ) ^ (j - 1) / d := by positivity
      nlinarith [mul_pos hd0 hL0, mul_pos (mul_pos hd0 hL0) hρ0]
    · left
      push Not at h8
      have e : (L : ℝ) ^ (j - 1) < 32 * d := by
        rw [div_lt_iff₀ hd0] at h8
        linarith
      rw [hpow]
      nlinarith
  · left
    have : j = 1 := by omega
    subst this
    simp only [pow_one]
    nlinarith

theorem holder_final_I {K1 K2 B X θ eF M : ℝ} (hK1 : K1 ≤ B) (hK2 : K2 ≤ B) (hθ : 0 < θ)
    (hX : 0 ≤ X) (heF : 0 ≤ eF) (hM : 0 ≤ M) :
    K1 / θ * X * eF + K2 / θ * X * M ≤ B / θ * X * (eF + M) := by
  have h1 : K1 / θ ≤ B / θ := div_le_div_of_nonneg_right hK1 hθ.le
  have h2 : K2 / θ ≤ B / θ := div_le_div_of_nonneg_right hK2 hθ.le
  have h3 : K1 / θ * X * eF ≤ B / θ * X * eF :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hX) heF
  have h4 : K2 / θ * X * M ≤ B / θ * X * M :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hX) hM
  linarith

/-- **The Hölder bound** (Proposition 4.9 with an arbitrary neighbourhood bound `M`). -/
theorem holder_bound (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ}
      (G : GeneratingSet d L N₀ k ϱ) (S : PtSetting G) {Mf : ℝ}, 0 ≤ Mf → (∀ i, ‖S.f i‖ ≤ Mf) →
      ∀ {x : Torus d (N₀ * L ^ k)}, x ∈ G.Ω 1 → ∀ {z : Fin d → ℤ}, 1 ≤ ‖z‖ →
      liftPt x z ∈ G.Ω 1 →
      ((G.layerIndex x = 1 ∧ G.pathDist x (liftPt x z) ≤ ENNReal.ofReal 1) ∨
        (2 ≤ G.layerIndex x ∧ (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (G.layerIndex x - 1))) →
      ∀ (ν : Fin d) {t : ℝ}, 0 ≤ t → ENNReal.ofReal t ≤ G.pathDist x S.y' → ∀ {M : ℝ}, 0 ≤ M →
      (∀ q ∈ G.Ω 1, G.pathDist q x ≤ ENNReal.ofReal (2 * d + 1) → S.U q ≤ M) →
      (G.spacing x) ^ 2 * ‖(S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
          (S.ut (x + Pi.single ν 1) - S.ut x)‖ ≤
        (B / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
          (Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf) + M) := by
  obtain ⟨Cc, hCc, hLoc⟩ := loc_lift_c hd
  obtain ⟨cH, hcH, hHs⟩ := green_holder_sum hd
  refine ⟨holderConst d L Cc cH, holderConst_nonneg hCc hcH, ?_⟩
  intro θ hθ0 hθ1 k N₀ _ ϱ G S Mf hMf0 hMf x hx z hz1 hx'Ω hpair ν t ht0 ht M hM0 hM
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
  obtain ⟨hdist, hsp⟩ := holder_pair_facts G S.hϱ hx hx'Ω hpair
  set j := G.layerIndex x with hj
  have hsp_eq : G.spacing x = (L : ℝ) ^ j := rfl
  have hθ' : 1 ≤ 1 / θ := by rw [le_div_iff₀ hθ0]; linarith
  have hX0 : 0 < (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) := by
    have := spacing_pos G (x := x)
    have : (0 : ℝ) < ‖z‖ := by linarith
    positivity
  have hEF : 0 ≤ Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf) := by positivity
  by_cases hI : 2 ≤ j ∧ 8 ≤ (1 / 4 : ℝ) * (L : ℝ) ^ (j - 1) / d ∧
      ‖z‖ ≤ ((1 / 4 : ℝ) * (L : ℝ) ^ (j - 1) / d) / 4
  · obtain ⟨hj2, hρ8, hzρ⟩ := hI
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, j = j₀ + 1 := ⟨j - 1, by omega⟩
    have hj01 : 1 ≤ j₀ := by omega
    have hρ' : 8 ≤ (1 / 4 : ℝ) * (L : ℝ) ^ j₀ / d := by
      have : j - 1 = j₀ := by omega
      rwa [this] at hρ8
    have hzρ' : ‖z‖ ≤ ((1 / 4 : ℝ) * (L : ℝ) ^ j₀ / d) / 4 := by
      have : j - 1 = j₀ := by omega
      rwa [this] at hzρ
    have hxl' : x ∈ G.layer (j₀ + 1) := by rw [← hj₀]; exact hxl
    have hjk' : j₀ + 1 ≤ k := by rw [← hj₀]; exact hjk
    have hLc := hLoc x S.ut hρ' z (r := ‖z‖) le_rfl hzρ' ν
    have hH : ∀ {R : ℝ}, 0 ≤ R → ∀ A : Finset (Fin d → ℤ),
        A.card ≤ (latticeBall (0 : Fin d → ℤ) R).card →
        ∑ w ∈ A, |greenDiff d ν (0 - w + z) - greenDiff d ν (0 - w)| ≤
          cH / θ * (‖z‖ + ‖z‖ ^ (1 - θ) * (R + 1) ^ θ) :=
      fun {R} hR A hA => hHs hθ0 hθ1 hz1 z le_rfl ν hR A hA 0
    have h1 := S.holder_caseI hCc hcH (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num) hj01 hjk'
      hxl' hρ' hz1 hzρ' hθ0 hθ1 ν hMf0 hMf ht0 ht hM0 hM hLc hH
    rw [hsp_eq, hj₀]
    refine h1.trans ?_
    have hX' : 0 ≤ ((L : ℝ) ^ (j₀ + 1)) ^ θ * ‖z‖ ^ (1 - θ) := by
      rw [hsp_eq, hj₀] at hX0; exact hX0.le
    have hq := holderKl2_nonneg d L (1 / 4)
    have hE1 := (Real.exp_pos (agmonRate d / 2 * (2 * d + 1))).le
    have hL0 : (0 : ℝ) ≤ L := by linarith
    have hK3 : 0 ≤ ((L : ℝ) + 1) * (32 * d * L) := by positivity
    refine holder_final_I (B := holderConst d L Cc cH) ?_ ?_ hθ0 hX' hEF hM0
    · unfold holderConst
      have : 0 ≤ 16 * (L : ℝ) ^ 2 * cH := by positivity
      linarith
    · unfold holderConst
      have h5 : 0 ≤ Cc * (d * L / (1 / 4 : ℝ)) ^ 2 * holderKl2 d L (1 / 4) := by positivity
      have h6 : 0 ≤ 3 * (L : ℝ) ^ 2 * cH * Real.exp (agmonRate d / 2 * (2 * d + 1)) := by positivity
      linarith
  · -- Case 1 / large distance
    have hcases := holder_scale_cases hj1 hI hd1
    have h2 := S.holder_caseII hx hx'Ω hdist hsp ν hM
    have hsp0 := spacing_pos G (x := x)
    have hℓ1 : (1 : ℝ) ≤ G.spacing x := by rw [hsp_eq]; exact one_le_pow₀ hL1
    have hK1 : (1 : ℝ) ≤ 32 * d * L := by nlinarith
    have hℓK := le_const_rpow_mul hℓ1 hz1 hK1 hθ0 hθ1 (by rw [hsp_eq]; exact hcases)
    set Dn := ‖(S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
          (S.ut (x + Pi.single ν 1) - S.ut x)‖ with hDn
    have hD0 : 0 ≤ Dn := norm_nonneg _
    set X := (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) with hXdef
    have hL0 : (0 : ℝ) ≤ L := by linarith
    have h3 : (G.spacing x) ^ 2 * Dn ≤ (32 * d * L * X) * ((L + 1) * M) := by
      calc (G.spacing x) ^ 2 * Dn = G.spacing x * (G.spacing x * Dn) := by ring
        _ ≤ G.spacing x * ((L + 1) * M) := mul_le_mul_of_nonneg_left h2 hsp0.le
        _ ≤ (32 * d * L * X) * ((L + 1) * M) :=
            mul_le_mul_of_nonneg_right hℓK (by positivity)
    refine h3.trans ?_
    have hB : ((L : ℝ) + 1) * (32 * d * L) ≤ holderConst d L Cc cH := by
      unfold holderConst
      have hq := holderKl2_nonneg d L (1 / 4)
      have h5 : 0 ≤ Cc * (d * L / (1 / 4 : ℝ)) ^ 2 * holderKl2 d L (1 / 4) := by positivity
      have h6 : 0 ≤ 3 * (L : ℝ) ^ 2 * cH * Real.exp (agmonRate d / 2 * (2 * d + 1)) := by
        have := (Real.exp_pos (agmonRate d / 2 * (2 * d + 1))).le
        positivity
      have h7 : 0 ≤ 16 * (L : ℝ) ^ 2 * cH := by positivity
      linarith
    have hX0' : 0 ≤ X := hX0.le
    have hθ1' : 1 ≤ 1 / θ := hθ'
    have hBn : 0 ≤ holderConst d L Cc cH := holderConst_nonneg hCc hcH
    calc (32 * d * L * X) * ((L + 1) * M) = (((L : ℝ) + 1) * (32 * d * L)) * (X * M) := by ring
      _ ≤ holderConst d L Cc cH * (X * M) :=
          mul_le_mul_of_nonneg_right hB (by positivity)
      _ ≤ holderConst d L Cc cH / θ * X * M := by
          have : holderConst d L Cc cH * (X * M) ≤ holderConst d L Cc cH * (1 / θ) * (X * M) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            nlinarith
          calc _ ≤ _ := this
            _ = _ := by ring
      _ ≤ holderConst d L Cc cH / θ * X * (Real.exp (-(agmonRate d / 2 * t)) *
          ((L : ℝ) ^ (2 * S.j') * Mf) + M) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith

/-- **Proposition 4.9 (G-2(iii), Hölder bound for `∂u`, exponent `1 - θ`, constant `B/θ`).**
Let `u = H_D(α)⁻¹ f` with `f` supported in the `j'`-block of `y'` and `|f| ≤ M_f`.  For a Hölder
pair `(x, x + z)` (`z ≠ 0`, `x + z` within path distance `1`: `ℓ(x) = L` or `d ‖z‖ ≤ ℓ(x)/L`),
`ℓ(x)^{2-θ} ‖z‖^{-(1-θ)} |∂_ν u(x + z) - ∂_ν u(x)| ≤ (B/θ) e^{-(ε₀/2) d(x, y')} ℓ_{j'}² M_f`
(stated multiplied out), with `B = B(d, L)` independent of `θ ∈ (0, 1)`; the left side vanishes if
`d(x, y') = ∞`. -/
theorem prop49 (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ}
      (G : GeneratingSet d L N₀ k ϱ) (S : PtSetting G) {Mf : ℝ}, 0 ≤ Mf → (∀ i, ‖S.f i‖ ≤ Mf) →
      ∀ {x : Torus d (N₀ * L ^ k)}, x ∈ G.Ω 1 → ∀ {z : Fin d → ℤ}, 1 ≤ ‖z‖ →
      liftPt x z ∈ G.Ω 1 →
      ((G.layerIndex x = 1 ∧ G.pathDist x (liftPt x z) ≤ ENNReal.ofReal 1) ∨
        (2 ≤ G.layerIndex x ∧ (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (G.layerIndex x - 1))) →
      ∀ (ν : Fin d),
      (G.pathDist x S.y' ≠ ⊤ →
        (G.spacing x) ^ 2 * ‖(S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
            (S.ut (x + Pi.single ν 1) - S.ut x)‖ ≤
          (B / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
            (Real.exp (-(agmonRate d / 2 * (G.pathDist x S.y').toReal)) *
              ((L : ℝ) ^ (2 * S.j') * Mf))) ∧
      (G.pathDist x S.y' = ⊤ →
        (S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
            (S.ut (x + Pi.single ν 1) - S.ut x) = 0) := by
  classical
  obtain ⟨B0, hB0, hHB⟩ := holder_bound hd hL
  obtain ⟨K2, hK2, h48⟩ := prop48 hd hL
  have hexp0 : 0 < Real.exp (agmonRate d / 2 * (2 * d + 1)) := Real.exp_pos _
  refine ⟨B0 * (1 + K2 * Real.exp (agmonRate d / 2 * (2 * d + 1))), by positivity, ?_⟩
  intro θ hθ0 hθ1 k N₀ _ ϱ G S Mf hMf0 hMf x hx z hz1 hx'Ω hpair ν
  have hε0 := agmonRate_pos S.hd0
  set D0 : ℝ := 2 * d + 1 with hD0
  have hD00 : 0 ≤ D0 := by positivity
  set F : ℝ := (L : ℝ) ^ (2 * S.j') * Mf with hF
  have hF0 : 0 ≤ F := by positivity
  have hnear : ∀ {a b : Torus d (N₀ * L ^ k)}, G.pathDist a S.y' ≠ ⊤ →
      G.pathDist b a ≤ ENNReal.ofReal D0 → G.pathDist b S.y' ≠ ⊤ := by
    intro a b ha hba
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ha⟩)
      ((G.pathDist_triangle b a S.y').trans (add_le_add hba le_rfl))
  have hsp0 := spacing_pos G (x := x)
  have hX0 : 0 ≤ (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) := by
    have : (0 : ℝ) < ‖z‖ := by linarith
    positivity
  refine ⟨fun hxt => ?_, fun hxt => ?_⟩
  · set τ := (G.pathDist x S.y').toReal with hτ
    have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
    have hM : ∀ q ∈ G.Ω 1, G.pathDist q x ≤ ENNReal.ofReal D0 →
        S.U q ≤ K2 * Real.exp (-(agmonRate d / 2 * (τ - D0))) * F := by
      intro q hq hqx
      have hqt : G.pathDist q S.y' ≠ ⊤ := hnear hxt hqx
      have h1 := (h48 G S hMf0 hMf hq).1 hqt
      refine h1.trans ?_
      have hlow : τ - D0 ≤ (G.pathDist q S.y').toReal := by
        have h1 : G.pathDist x S.y' ≤ ENNReal.ofReal D0 + G.pathDist q S.y' := by
          refine (G.pathDist_triangle x q S.y').trans (add_le_add ?_ le_rfl)
          rw [GeneratingSet.pathDist_comm]; exact hqx
        have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hqt⟩) h1
        rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hqt, ENNReal.toReal_ofReal hD00] at h2
        linarith
      apply mul_le_mul_of_nonneg_right _ hF0
      apply mul_le_mul_of_nonneg_left _ hK2
      apply Real.exp_le_exp.2
      nlinarith
    have hM0 : 0 ≤ K2 * Real.exp (-(agmonRate d / 2 * (τ - D0))) * F := by positivity
    have h := hHB hθ0 hθ1 G S hMf0 hMf hx hz1 hx'Ω hpair ν hτ0
      (ENNReal.ofReal_toReal hxt).le hM0 hM
    refine h.trans (le_of_eq ?_)
    have e : Real.exp (-(agmonRate d / 2 * (τ - D0))) =
        Real.exp (-(agmonRate d / 2 * τ)) * Real.exp (agmonRate d / 2 * D0) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    ring
  · -- infinite distance: the bound holds for every `t` with `M = 0`
    have hM : ∀ q ∈ G.Ω 1, G.pathDist q x ≤ ENNReal.ofReal D0 → S.U q ≤ 0 := by
      intro q hq hqx
      have hqt : G.pathDist q S.y' = ⊤ := by
        by_contra hne
        have : G.pathDist x S.y' ≠ ⊤ := by
          have := hnear (a := q) (b := x) hne (by rw [GeneratingSet.pathDist_comm]; exact hqx)
          exact this
        exact this hxt
      exact ((h48 G S hMf0 hMf hq).2 hqt).le
    have hbound : ∀ t : ℝ, 0 ≤ t →
        (G.spacing x) ^ 2 * ‖(S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
            (S.ut (x + Pi.single ν 1) - S.ut x)‖ ≤
          (B0 / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
            (Real.exp (-(agmonRate d / 2 * t)) * F + 0) := by
      intro t ht0
      exact hHB hθ0 hθ1 G S hMf0 hMf hx hz1 hx'Ω hpair ν ht0 (by rw [hxt]; exact le_top)
        le_rfl hM
    have hlim : Filter.Tendsto (fun t : ℝ => (B0 / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
        (Real.exp (-(agmonRate d / 2 * t)) * F + 0)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun t : ℝ => agmonRate d / 2 * t) Filter.atTop Filter.atTop :=
        Filter.tendsto_id.const_mul_atTop (by positivity)
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
      have h3 := (h2.mul_const F).add_const 0
      have h4 := h3.const_mul ((B0 / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)))
      simpa using h4
    have hle := ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨0, fun t ht => hbound t ht⟩)
    have hsq : 0 < (G.spacing x) ^ 2 := by positivity
    have hn : ‖(S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
        (S.ut (x + Pi.single ν 1) - S.ut x)‖ ≤ 0 := by
      by_contra hpos
      push Not at hpos
      have := mul_pos hsq hpos
      linarith
    exact norm_le_zero_iff.1 hn

end Balaban.Multiscale
