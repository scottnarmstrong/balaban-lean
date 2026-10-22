/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalBoxFinal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The small-field last integral at a whitening, from the local form and the closeness

A6-3 (blocker 5, small-field half), the statement of `FinalSmallFieldInput` at a whitening `A` of
the Gaussian variable (a parameter of the theorem; the spine definition `sfBoxIntegral` is its
instance at the localized square root, reading B-1′ of `notes/phase1/PLAN-B.md`).

`finalSmallFieldInput_of_localForm`: for families `W`, `U` of local terms and a whitening `A` of the
class-member data, a cell side `Mc` of the constants, if

* `hW` (B1): for every target `η > 0` and `β` large, on every torus of the family the fluctuation
  integrand at the whitening has the local form `BoxLocalForm` at the cutoff `p₁ = cut κ c₉ β_k`,
  with the numerical conditions of the cell gas, the rate `κ + log 2 ≤ κ_g/3^d - 1` and the
  amplitude `boxAmp ≤ η L^{-(k+1)θ}`;
* `hC` (A2, blocker 7): the two-torus closeness of the per-torus activities `lastSfAct`, at the rate
  `κ + log 2`, with a margin `t₀` and a rate `λ ≥ κ + log 2` fixed before `β`, and the amplitude
  `a_C e^{κ + log 2} ≤ (c₉/8) L^{-(k+1)θ}`;

then for `β` large, on every torus of the family and every source of the unit `ℓ¹` ball,
`Ξ_box(A) = exp(E + ⟨g, h⟩ + Σ_{j ≤ k} Σ_X q_j + Σ_X a)` with `a` in Root-F's form at the scale
`k + 1` (`ObservableActivitiesAt … κ (c₉/2) δ (k+1) kf a`). The class data of the remainder terms
come from `FlatRep` (`SFFlat2.rTerms`, the standing hypotheses `BgHyp` at the scale `k`, `β_k` from
`RunningHypTo`), the rate tie from `PrefixInput` (`c1_mul_rate_le`).
-/

@[expose] public section

open MeasureTheory Finset Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField
  Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Localization Balaban.Green Balaban.RootFSpine.LastScale
  Balaban.Inhabited.RootBoundsArith

namespace Balaban.RootFSpine

/-- `β_k ≥ e^{-1/20} β L^{k(d-2)}` gives `β_k^{-2} ≤ e^{1/10} (β L^{k(d-2)})^{-2}`. -/
theorem inv_sq_le_of_running {d L k : ℕ} {β βk γ : ℝ} (hβ : 0 < β) (hL : (0 : ℝ) < L) (hγ0 : 0 < γ)
    (hγ : |Real.log γ| ≤ 1 / 20) (hβk : βk = β * (L : ℝ) ^ (k * (d - 2)) * γ) :
    (βk⁻¹) ^ 2 ≤ Real.exp (1 / 10) *
      ((Balaban.LargeField.ActionConv.betaK d L k β) ^ 2)⁻¹ := by
  unfold Balaban.LargeField.ActionConv.betaK
  have hb : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hγl : Real.exp (-(1 / 20)) ≤ γ := by
    rw [← Real.exp_log hγ0]
    exact Real.exp_le_exp.2 (by linarith [neg_abs_le (Real.log γ)])
  have hγ2 : (γ ^ 2)⁻¹ ≤ Real.exp (1 / 10) := by
    have h1 : Real.exp (-(1 / 20)) ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le hγl 2
    have h2 : Real.exp (-(1 / 20)) ^ 2 = (Real.exp (1 / 10))⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]; norm_num
    rw [h2] at h1
    have := inv_anti₀ (by positivity) h1
    rwa [inv_inv] at this
  rw [hβk, show (β * (L : ℝ) ^ (k * (d - 2)) * γ)⁻¹ ^ 2 =
    ((β * (L : ℝ) ^ (k * (d - 2))) ^ 2)⁻¹ * (γ ^ 2)⁻¹ by rw [inv_pow, mul_pow, mul_inv]]
  calc ((β * (L : ℝ) ^ (k * (d - 2))) ^ 2)⁻¹ * (γ ^ 2)⁻¹
      ≤ ((β * (L : ℝ) ^ (k * (d - 2))) ^ 2)⁻¹ * Real.exp (1 / 10) :=
        mul_le_mul_of_nonneg_left hγ2 (by positivity)
    _ = _ := by ring

section Spine

variable (d N : ℕ) (δ : ℝ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ) (cut : ℝ → ℝ → ℝ → ℝ)

/-- **The small-field last integral at a whitening, from the local form and the closeness**
(A6-3; P4 (6.6), P7 (4.9)–(4.17), P5 (2.39); the statement of `FinalSmallFieldInput` at the box
integral `ctxBoxIntegralL` of the whitening `A`). The hypotheses: the prefix (`PrefixInput`), the
typing of `δ`, the local form `hW` with its numerical conditions (B1), and the two-torus closeness
`hC` of the per-torus activities `lastSfAct` (A2, blocker 7). -/
theorem finalSmallFieldInput_of_localForm (hPre : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ ((d : ℝ) - 2) / 2) (Mc : ℝ → ℝ → ℕ)
    (A : ∀ (κ c₉ β ν : ℝ) (kf k : ℕ) [NeZero (T κ c₉).L] [NeZero (T κ c₉).M] (R : ℕ → ℝ)
      (geo : ∀ (nK : ℕ) [NeZero nK],
        Geo 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) R (T κ c₉).M)
      (cs : OpConsts) (P : BudgetConsts)
      (_ : RepFam 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] R (kZero d (T κ c₉).L β ν) (kf + 1)
        (T κ c₉).M N geo cs P k (C7 κ c₉).m₁ (ϱ κ c₉))
      (_ : EuclideanSpace ℝ (Fin N)) (nK : ℕ) [NeZero nK],
      Matrix (BlockAt 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) k × Fin N)
        (BlockAt 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) k × Fin N) ℝ)
    (W : ∀ (κ c₉ β ν : ℝ) (kf k : ℕ) [NeZero (T κ c₉).L] [NeZero (T κ c₉).M] (R : ℕ → ℝ)
      (geo : ∀ (nK : ℕ) [NeZero nK],
        Geo 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) R (T κ c₉).M)
      (cs : OpConsts) (P : BudgetConsts)
      (_ : RepFam 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] R (kZero d (T κ c₉).L β ν) (kf + 1)
        (T κ c₉).M N geo cs P k (C7 κ c₉).m₁ (ϱ κ c₉))
      (_ : EuclideanSpace ℝ (Fin N)) (nK : ℕ) [NeZero nK],
      Finset (BlockAt 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) k) →
        (BlockAt 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) k × Fin N → ℂ) →
        (GIdx 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) N → ℂ) → ℂ)
    (U : ∀ (κ c₉ β ν : ℝ) (kf k : ℕ) [NeZero (T κ c₉).L] [NeZero (T κ c₉).M] (R : ℕ → ℝ)
      (geo : ∀ (nK : ℕ) [NeZero nK],
        Geo 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) R (T κ c₉).M)
      (cs : OpConsts) (P : BudgetConsts)
      (_ : RepFam 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] R (kZero d (T κ c₉).L β ν) (kf + 1)
        (T κ c₉).M N geo cs P k (C7 κ c₉).m₁ (ϱ κ c₉))
      (_ : EuclideanSpace ℝ (Fin N)) (nK : ℕ) [NeZero nK],
      Finset (BlockAt 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) k) →
        (BlockAt 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) k × Fin N → ℝ) → ℂ)
    (hW : ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∀ η : ℝ, 0 < η → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
      ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
      ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
      ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
      ∀ k : ℕ, 1 ≤ k → k ≤ kf →
      ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ) hM6 hkK R geo cs P F St vc,
        FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
          (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk →
        7 / 8 < νk * ((T κ c₉).L : ℝ) ^ 2 →
        ∃ G₀ Rt a ε εU κg : ℝ, 0 < cut κ c₉ (F.sf.β k) ∧ 0 < Mc κ c₉ ∧
          Mc κ c₉ ≤ (T κ c₉).M * (T κ c₉).L ∧ 0 ≤ κg ∧ κg + 12 * d + 21 / 2 ≤ a ∧
          κ + Real.log 2 ≤ κg / 3 ^ d - 1 ∧
          ((2 * Mc κ c₉ : ℕ) : ℝ) ^ d * (ε + εU) ≤ 1 / 2 ∧
          boxAmp d (T κ c₉).M (T κ c₉).L (Mc κ c₉) (ε + εU) Rt ≤
            η * ((T κ c₉).L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) ∧
          ∀ (nK : ℕ) [NeZero nK], BoxLocalForm (F.ctx hM6 hkK nK) vc h
            (A κ c₉ β ν kf k R geo cs P F h nK) (cut κ c₉ (F.sf.β k)) G₀ Rt (Mc κ c₉) a ε εU
            (W κ c₉ β ν kf k R geo cs P F h nK) (U κ c₉ β ν kf k R geo cs P F h nK))
    (hC : ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ (lam : ℝ) (t₀ : ℕ), κ + Real.log 2 ≤ lam ∧
      ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
      ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
      ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
      ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
      ∀ k : ℕ, 1 ≤ k → k ≤ kf →
      ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ) hM6 hkK R geo cs P F St vc,
        FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
          (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk →
        7 / 8 < νk * ((T κ c₉).L : ℝ) ^ 2 →
        ∃ aC : ℝ, 0 ≤ aC ∧ aC * Real.exp (κ + Real.log 2) ≤
            c₉ / 8 * ((T κ c₉).L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) ∧
          LastScaleTwoTorusClose d N (T κ c₉).L (T κ c₉).M kf k (κ + Real.log 2) aC lam t₀
            (lastSfAct (W κ c₉ β ν kf k R geo cs P F h) (U κ c₉ β ν kf k R geo cs P F h)
              (Mc κ c₉) (cut κ c₉ (F.sf.β k)) F.sf (P6 κ c₉).m₀ h)) :
    ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
    ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
    ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
    ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
    ∀ k : ℕ, 1 ≤ k → k ≤ kf →
    ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ) hM6 hkK R geo cs P F St vc,
      FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk →
      7 / 8 < νk * ((T κ c₉).L : ℝ) ^ 2 →
      ∃ (aa : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (E : ℕ → ℂ),
        ObservableActivitiesAt d N (T κ c₉).L (T κ c₉).M κ (c₉ / 2) δ (k + 1) kf aa ∧
        ∀ (nK : ℕ) [NeZero nK]
          (g : GIdx 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
            (kf + 1) N → ℂ), g ∈ LargeField.l1Ball _ →
          ctxBoxIntegralL (F.ctx hM6 hkK nK) vc h (A κ c₉ β ν kf k R geo cs P F h nK)
              (cut κ c₉ (F.sf.β k)) g =
            Complex.exp (E nK + ∑ x, ∑ i, g (x, i) * (h i : ℂ)
            + ∑ j ∈ Finset.Icc 1 k, ∑ X,
              inhObs F.sf (P6 κ c₉).m₀ h
                ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) * (T κ c₉).L ^ (kf + 1)) j X
                (fun x i => g (x, i))
            + ∑ X, aa ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) * (T κ c₉).L ^ (kf + 1))
                (k + 1) X (fun x i => g (x, i))) := by
  intro κ hκ c₉ hc₉
  obtain ⟨hL3, -, -, -, hMc', h14, hM1, -, hadm, -, -, -, -, hκP, -, hTy, hϱ, -, -, -, -⟩ :=
    hPre κ hκ c₉ hc₉
  have hd : 3 ≤ d := hTy.1.three_le_d
  obtain ⟨lam, t₀, hlam, β₀C, hC'⟩ := hC κ hκ c₉ hc₉
  set κ' : ℝ := κ + Real.log 2 with hκ'
  set T₀ : ℝ := 1 + 2 * Real.exp (κ' * (t₀ : ℝ)) with hT₀def
  have hT₀ : 0 < T₀ := by positivity
  have hT₀ne : T₀ ≠ 0 := hT₀.ne'
  obtain ⟨β₀W, hW'⟩ := hW κ hκ c₉ hc₉ (c₉ / 16 / T₀) (by positivity)
  obtain ⟨β₀M, hM'⟩ := measInt_sfFactor2_of_flatRep d N δ T P6 C7 PB cs₀ M1 c rH ϱ hPre κ hκ c₉ hc₉
  set θ : ℝ := ((d : ℝ) - 2) / 2 + δ with hθ
  set CR : ℝ := 2 * (((P6 κ c₉).m₀ + (C7 κ c₉).m₁ : ℕ) : ℝ) * Real.exp (P6 κ c₉).κ *
    Real.exp (1 / 10) * T₀ with hCR
  have hCR0 : 0 ≤ CR := by positivity
  set β₀R : ℝ := max 2 (Real.sqrt ((CR + 1) * ((T κ c₉).L : ℝ) ^ θ / (c₉ / 16))) with hβ₀R
  refine ⟨max (max β₀C β₀W) (max β₀M β₀R), fun β hβ ν hν hνL h hh kf hkf _ _ k hk1 hkkf ρ νk
    hM6 hkK R geo cs P F St vc hF hstop => ?_⟩
  have hβC : β₀C ≤ β := (le_max_left _ _).trans ((le_max_left _ _).trans hβ)
  have hβW : β₀W ≤ β := (le_max_right _ _).trans ((le_max_left _ _).trans hβ)
  have hβM : β₀M ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβR : β₀R ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hβ2 : 2 ≤ β := (le_max_left _ _).trans hβR
  obtain ⟨aC, haC0, haC, hCl⟩ := hC' β hβC ν hν hνL h hh kf hkf k hk1 hkkf ρ νk hM6 hkK R geo cs P F
    St vc hF hstop
  obtain ⟨G₀, Rt, a, ε, εU, κg, hp1, hMc, hMcL, hκg, ha, hrate, hεc, hampB, hWf⟩ :=
    hW' β hβW ν hν hνL h hh kf hkf k hk1 hkkf ρ νk hM6 hkK R geo cs P F St vc hF hstop
  have hF' := hF
  obtain ⟨-, -, -, -, -, -, -, -, hrep, -, -, hνkF, hrun, -, hν9⟩ := hF'
  have hsf := hrep.sfData
  obtain ⟨-, -, -, -, -, -, -, -, hbeta, -⟩ := hrun
  obtain ⟨γk, hγk0, hγk, hβk⟩ := hbeta k le_rfl
  have hLpos : (0 : ℝ) < (T κ c₉).L := by exact_mod_cast (by omega : 0 < (T κ c₉).L)
  have hL1 : (1 : ℝ) ≤ (T κ c₉).L := by exact_mod_cast (by omega : 1 ≤ (T κ c₉).L)
  have hβk1 : 1 ≤ F.sf.β k := by
    rw [hβk]
    have hγl : Real.exp (-(1 / 20)) ≤ γk := by
      rw [← Real.exp_log hγk0]
      exact Real.exp_le_exp.2 (by linarith only [neg_abs_le (Real.log γk), hγk])
    have he : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 20)) := by
      have := Real.add_one_le_exp (-(1 / 20) : ℝ); linarith only [this]
    have hpw : (1 : ℝ) ≤ ((T κ c₉).L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
    calc (1 : ℝ) = 2 * 1 * (1 / 2) := by norm_num
      _ ≤ β * ((T κ c₉).L : ℝ) ^ (k * (d - 2)) * γk := by
          refine mul_le_mul (mul_le_mul hβ2 hpw (by norm_num) (by linarith only [hβ2])) (he.trans hγl)
            (by norm_num) (by positivity)
  have hνs : 0 < F.sf.ν k := hsf.coeff.nu_pos
  have hνs9 : F.sf.ν k ≤ 1 := by rw [hνkF]; linarith only [hν9]
  have hBgR : BgHyp d (T κ c₉).L k (ϱ κ c₉) (aIdeal (T κ c₉).L k (F.sf.a k))
      (Def6.bgMass (T κ c₉).L k (F.sf.β k) (F.sf.ν k)) :=
    bgHyp_of_ideal hd hL3 hϱ hsf.coeff.a_ge hsf.coeff.a_lt (Def6.bgMass_nonneg hνs _ _)
      ((bgMass_mul_sq_le hLpos hνs _).trans hνs9)
  have hεk := eps_pos_of_admissible hadm k
  have hκf := (c1_mul_rate_le (d := d) hL3 hκ).trans hκP
  have hs4 : 4 ≤ (T κ c₉).M * (T κ c₉).L ^ (k + 1) := by
    have hM14 : 14 ≤ (T κ c₉).M := by
      rw [hMc']
      calc 14 ≤ c κ c₉ := h14
        _ = c κ c₉ * 1 := (mul_one _).symm
        _ ≤ c κ c₉ * M1 κ c₉ := Nat.mul_le_mul_left _ hM1
    have h1 : 1 ≤ (T κ c₉).L ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    calc 4 ≤ (T κ c₉).M := by omega
      _ = (T κ c₉).M * 1 := (mul_one _).symm
      _ ≤ (T κ c₉).M * (T κ c₉).L ^ (k + 1) := Nat.mul_le_mul_left _ h1
  -- the amplitude condition of the conversion (with `c₉/2`)
  set Λ : ℝ := ((T κ c₉).L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * θ)) with hΛ
  have hΛ0 : 0 ≤ Λ := Real.rpow_nonneg hLpos.le _
  set BR : ℝ := 2 * (((P6 κ c₉).m₀ + (C7 κ c₉).m₁ : ℕ) : ℝ) * ((F.sf.β k)⁻¹) ^ 2 *
    Real.exp (P6 κ c₉).κ with hBR
  set Bbox : ℝ := boxAmp d (T κ c₉).M (T κ c₉).L (Mc κ c₉) (ε + εU) Rt with hBbox
  have hRbound : T₀ * BR ≤ c₉ / 16 * Λ := by
    have h1 := inv_sq_le_of_running (d := d) (L := (T κ c₉).L) (k := k) (by linarith only [hβ2])
      hLpos hγk0 hγk hβk
    have hβsq : ((T κ c₉).L : ℝ) ^ θ ≤ c₉ / 16 / (CR + 1) * β ^ 2 := by
      have hs : Real.sqrt ((CR + 1) * ((T κ c₉).L : ℝ) ^ θ / (c₉ / 16)) ≤ β :=
        (le_max_right _ _).trans hβR
      have hsq := Real.sqrt_le_iff.1 hs
      have hpos : 0 ≤ (CR + 1) * ((T κ c₉).L : ℝ) ^ θ / (c₉ / 16) := by positivity
      have h2 := hsq.2
      rw [div_le_iff₀ (by positivity)] at h2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith only [h2]
    have h3 := rest_small_in_beta (d := d) (L := (T κ c₉).L) (k := k) hd (by omega)
      (by positivity : (0 : ℝ) < c₉ / 16) hCR0 (by linarith only [hβ2]) hδ0 hδ hβsq
    calc T₀ * BR = (2 * (((P6 κ c₉).m₀ + (C7 κ c₉).m₁ : ℕ) : ℝ) * Real.exp (P6 κ c₉).κ * T₀) *
          ((F.sf.β k)⁻¹) ^ 2 := by rw [hBR]; ring
      _ ≤ (2 * (((P6 κ c₉).m₀ + (C7 κ c₉).m₁ : ℕ) : ℝ) * Real.exp (P6 κ c₉).κ * T₀) *
          (Real.exp (1 / 10) * ((Balaban.LargeField.ActionConv.betaK d (T κ c₉).L k β) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = CR * ((Balaban.LargeField.ActionConv.betaK d (T κ c₉).L k β) ^ 2)⁻¹ := by rw [hCR]; ring
      _ ≤ _ := h3
  have hamp : (Bbox + BR) + aC * Real.exp κ' + 2 * (Bbox + BR) * Real.exp (κ' * (t₀ : ℝ)) ≤
      c₉ / 2 / 2 * Λ := by
    have hBb : T₀ * Bbox ≤ c₉ / 16 * Λ := by
      have := mul_le_mul_of_nonneg_left hampB hT₀.le
      calc T₀ * Bbox ≤ T₀ * (c₉ / 16 / T₀ * Λ) := this
        _ = c₉ / 16 * Λ := by field_simp
    calc (Bbox + BR) + aC * Real.exp κ' + 2 * (Bbox + BR) * Real.exp (κ' * (t₀ : ℝ))
        = T₀ * Bbox + T₀ * BR + aC * Real.exp κ' := by rw [hT₀def]; ring
      _ ≤ c₉ / 16 * Λ + c₉ / 16 * Λ + c₉ / 8 * Λ := add_le_add (add_le_add hBb hRbound) haC
      _ ≤ c₉ / 2 / 2 * Λ := by linarith only [hΛ0]
  obtain ⟨aa, E, haa, hid⟩ := ctxFluctBoxIntegralL_eq_exp_of_boxLocalForm F hM6 hkK vc h hh
    (A κ c₉ β ν kf k R geo cs P F h) (W κ c₉ β ν kf k R geo cs P F h)
    (U κ c₉ β ν kf k R geo cs P F h) hWf hsf.rTerms hBgR hεk hβk1 (show 0 < d by omega) hk1 hkkf hs4 hMc
    hMcL hp1 (c₉ := c₉ / 2) (δ := δ) hκ hκg ha hrate hεc hκf haC0 hlam hCl hamp
  refine ⟨aa, fun nK => if hnK : nK ≠ 0 then
    (haveI : NeZero nK := ⟨hnK⟩; E nK + fluctVacConst (F.ctx hM6 hkK nK) vc h) else 0, haa,
    fun nK _ g hg => ?_⟩
  have hnK : nK ≠ 0 := NeZero.ne nK
  obtain ⟨HB, -, -⟩ := hM' β hβM ν hν hνL h hh kf hkf k hk1 hkkf ρ νk hM6 hkK R geo cs P F St vc
    hF hstop nK g hg
  have he : ∑ i, h i ^ 2 = 1 := sum_sq_eq_one_of_norm_eq_one h hh
  rw [ctxBoxIntegralL_eq_exp_of_fluct (F.ctx hM6 hkK nK) vc h HB he hk1 _ _ g (hid nK g hg)]
  simp only [ne_eq, hnK, not_false_eq_true, ↓reduceDIte]
  rfl

end Spine

end Balaban.RootFSpine
