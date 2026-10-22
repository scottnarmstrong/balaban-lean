/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalBoxAct
public import Balaban.Spine.FinalBoxRTerm
public import Balaban.Spine.FinalAmplitude
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The box integral of a member of the class from the local form

A6-3, gas layer, the assembly for one member of the class at the stopping scale (the generic core,
at a whitening `A` of each torus; the spine statement is its instance at the localized square root,
reading B-1′ of `notes/phase1/PLAN-B.md`).

* `torusClausesAt_boxAct`: the regrouped activities of the box gas (`boxAct`) have the four
  per-torus clauses of Root-F's form at the rate `κ'' ≤ κ_g/3^d - 1` and the amplitude `boxAmp`.
* `lastSfAct`: **the per-torus activities of the last scale** — the box activities of the torus of
  the family (`torusFam`) plus the remainder activities regrouped at the scale `k + 1`
  (`regroupFam` of `rObs`); `lastScaleTorusClauses_lastSfAct`: they satisfy `LastScaleTorusClauses`
  at the rate `κ + log 2` with the amplitude `boxAmp + 2 m β_k^{-2} e^{κ_flow}`.
* `ctxFluctBoxIntegralL_eq_exp_of_boxLocalForm`: under the local form on every torus
  (`BoxLocalForm`, B1), the numerical conditions, and the two-torus closeness of `lastSfAct`
  (`LastScaleTwoTorusClose`, A2), the box average of the fluctuation integrand at the whitening is
  `exp(E + Σ_X a(X; g))` with activities `a` of Root-F's form at the scale `k + 1`
  (`ObservableActivitiesAt`; through `observableActivitiesAt_of_twoTorusClose`).
-/

@[expose] public section

open MeasureTheory Finset Balaban Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2 Balaban.Green Balaban.Polymer Balaban.Multiscale Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Localization Balaban.Background Balaban.RootFSpine.LastScale
  Balaban.Inhabited.RootBoundsArith

namespace Balaban.RootFSpine

section Box

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- The amplitude of the box activities is nonnegative. -/
theorem boxAmp_nonneg {C : SFCtx S n R M K N k m₁ ϱ} {vc : CorrCoef S.d}
    {hv : EuclideanSpace ℝ (Fin N)}
    {A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ}
    {p1 G₀ Rt a ε εU : ℝ} {Mc : ℕ}
    {W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) → (GIdx S n M K N → ℂ) → ℂ}
    {U : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → ℂ}
    (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U) (hMc : 0 < Mc) (hp1 : 0 < p1)
    {κg : ℝ} (hκg : 0 ≤ κg) (ha : κg + 12 * S.d + 21 / 2 ≤ a)
    (hε : ((2 * Mc : ℕ) : ℝ) ^ S.d * (ε + εU) ≤ 1 / 2) :
    0 ≤ boxAmp S.d M S.L Mc (ε + εU) Rt := by
  have := boxKP_nonneg hW hMc hp1 hκg ha hε
  unfold boxAmp
  positivity

/-- **The box activities have the per-torus clauses of Root-F's form** at every rate
`κ'' ≤ κ_g/3^d - 1`, with the amplitude `boxAmp`. -/
theorem torusClausesAt_boxAct {C : SFCtx S n R M K N k m₁ ϱ} {vc : CorrCoef S.d}
    {hv : EuclideanSpace ℝ (Fin N)}
    {A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ}
    {p1 G₀ Rt a ε εU : ℝ} {Mc : ℕ}
    {W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) → (GIdx S n M K N → ℂ) → ℂ}
    {U : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → ℂ}
    (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U) (hMc : 0 < Mc) (hp1 : 0 < p1)
    (hk1 : k + 1 ≤ K) (hMcL : Mc ≤ M * S.L) {κg κ'' : ℝ} (hκg : 0 ≤ κg)
    (ha : κg + 12 * S.d + 21 / 2 ≤ a) (hε : ((2 * Mc : ℕ) : ℝ) ^ S.d * (ε + εU) ≤ 1 / 2)
    (hrate : κ'' ≤ κg / 3 ^ S.d - 1) :
    TorusClausesAt S.d N S.L M k κ'' (boxAmp S.d M S.L Mc (ε + εU) Rt) (M * n K * S.L ^ K)
      (boxAct W U Mc p1) := by
  have hk : k ≤ K := by omega
  refine ⟨fun X hX g => ?_, fun X => boxAct_analytic hW hMc hp1 hκg ha hε X,
    fun X g g' hgg => boxAct_local hW X 1 hgg, fun X g hg => ?_⟩
  · unfold boxAct
    rw [boxAct_support hW hMc hp1.le hk X hX, boxAct_support hW hMc hp1.le hk X hX]
  · refine (boxAct_bound hW hMc hp1 hk1 hMcL hκg ha hε X hg).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (boxAmp_nonneg hW hMc hp1 hκg ha hε))
    have hcast : ((M * S.L ^ (k + 1) : ℕ) : ℝ) = (M : ℝ) * (S.L : ℝ) ^ (k + 1) := by push_cast; ring
    rw [hcast]
    have hP : 0 ≤ (X.card : ℝ) / ((M : ℝ) * (S.L : ℝ) ^ (k + 1)) ^ S.d := by positivity
    have e1 : ∀ c : ℝ, -c * (X.card : ℝ) / ((M : ℝ) * (S.L : ℝ) ^ (k + 1)) ^ S.d =
        -c * ((X.card : ℝ) / ((M : ℝ) * (S.L : ℝ) ^ (k + 1)) ^ S.d) := fun c => by ring
    rw [e1, e1]
    nlinarith

end Box

section Last

variable {S : Setting} {R : ℕ → ℝ} {k0 kf M N : ℕ} [NeZero M] [NeZero S.L]
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L (kf + 1) nK) R M} {cs : OpConsts}
  {P : BudgetConsts} {P6 : Def6.Consts} {C7 : Consts7} {k : ℕ} {ϱ : ℝ}

/-- **The per-torus activities of the last scale** (A6-3; the activities `a_T` of the interface with
the two-torus agreement): on a side `ℓ`, the box activities of the torus of the family with that
side (`torusFam` of `boxAct`) plus the remainder activities of `𝒟_k` regrouped at the scale `k + 1`
(`regroupFam` of `rObs`). -/
noncomputable def lastSfAct
    (W : ∀ (nK : ℕ) [NeZero nK], Finset (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k) →
      (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k × Fin N → ℂ) →
      (GIdx S (sides S.L (kf + 1) nK) M (kf + 1) N → ℂ) → ℂ)
    (U : ∀ (nK : ℕ) [NeZero nK], Finset (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k) →
      (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k × Fin N → ℝ) → ℂ)
    (Mc : ℕ) (p1 : ℝ) (sf : SFData S.d S.L C7.m₁ k N ϱ) (m₀ : ℕ)
    (hv : EuclideanSpace ℝ (Fin N)) :
    (ℓ : ℕ) → Finset (Torus S.d ℓ) → (Torus S.d ℓ → Fin N → ℂ) → ℂ :=
  fun ℓ X g => torusFam M S.L (kf + 1) (fun nK _ => boxAct (W nK) (U nK) Mc p1) ℓ X g +
    regroupFam M S.L k (fun ℓ => rObs sf m₀ hv ℓ) ℓ (k + 1) X g


/-- **The per-torus clauses of the last-scale activities** (`LastScaleTorusClauses` at the rate
`κ + log 2`, the amplitude `boxAmp + 2 m β_k^{-2} e^{κ_flow}`): the box part on the tori of the
family (`torusClausesAt_boxAct`, `lastScaleTorusClauses_torusFam`) and the remainder part on every
admissible torus (`torusClausesAt_rObs` at the rate `κ_R - d log L - 1`,
`κ_R = κ + log 2 + d log L + 1`). -/
theorem lastScaleTorusClauses_lastSfAct (F : RepFam S R k0 (kf + 1) M N geo cs P k C7.m₁ ϱ)
    (hM6 : M = S.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ kf + 1) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
    (A : ∀ (nK : ℕ) [NeZero nK], Matrix (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k × Fin N)
      (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k × Fin N) ℝ)
    (W : ∀ (nK : ℕ) [NeZero nK], Finset (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k) →
      (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k × Fin N → ℂ) →
      (GIdx S (sides S.L (kf + 1) nK) M (kf + 1) N → ℂ) → ℂ)
    (U : ∀ (nK : ℕ) [NeZero nK], Finset (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k) →
      (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k × Fin N → ℝ) → ℂ)
    {p1 G₀ Rt a ε εU : ℝ} {Mc : ℕ}
    (hW : ∀ (nK : ℕ) [NeZero nK], BoxLocalForm (F.ctx hM6 hkK nK) vc hv (A nK) p1 G₀ Rt Mc a ε εU
      (W nK) (U nK))
    (hRt : ∀ (N₁ : ℕ) [NeZero N₁],
      RTermsH4 (ϱ := ϱ) P6 F.sf.β F.sf.ν F.sf.a N₁ (F.sf.Rt N₁) fun _ => 1)
    (hBgR : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (F.sf.a k))
      (Def6.bgMass S.L k (F.sf.β k) (F.sf.ν k)))
    (hεk : 0 < P6.eps S.d S.L k) (hβ : 1 ≤ F.sf.β k) (hk1 : 1 ≤ k) (hk : k ≤ kf)
    (hMc : 0 < Mc) (hMcL : Mc ≤ M * S.L) (hp1 : 0 < p1) {κ κg : ℝ} (hκ : 0 < κ) (hκg : 0 ≤ κg)
    (ha : κg + 12 * S.d + 21 / 2 ≤ a) (hrate : κ + Real.log 2 ≤ κg / 3 ^ S.d - 1)
    (hε : ((2 * Mc : ℕ) : ℝ) ^ S.d * (ε + εU) ≤ 1 / 2)
    (hκf : Fluctuation.c1 S.d S.L * (κ + Real.log 2 + S.d * Real.log S.L + 2) ≤ P6.κ) :
    LastScaleTorusClauses S.d N S.L M kf k (κ + Real.log 2)
      (boxAmp S.d M S.L Mc (ε + εU) Rt +
        2 * ((P6.m₀ + C7.m₁ : ℕ) : ℝ) * ((F.sf.β k)⁻¹) ^ 2 * Real.exp P6.κ)
      (lastSfAct W U Mc p1 F.sf P6.m₀ hv) := by
  have hL0 : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hML : 0 < M * S.L ^ (kf + 1) := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne M)) (pow_pos hL0 _)
  have hbox : LastScaleTorusClauses S.d N S.L M kf k (κ + Real.log 2)
      (boxAmp S.d M S.L Mc (ε + εU) Rt)
      (torusFam M S.L (kf + 1) (fun nK _ => boxAct (W nK) (U nK) Mc p1)) :=
    lastScaleTorusClauses_torusFam hML _ fun nK _ =>
      torusClausesAt_boxAct (hW nK) hMc hp1 (by omega) hMcL hκg ha hε hrate
  have hBbox : 0 ≤ boxAmp S.d M S.L Mc (ε + εU) Rt := by
    have : NeZero 1 := ⟨one_ne_zero⟩
    exact boxAmp_nonneg (hW 1) hMc hp1 hκg ha hε
  have hBR : 0 ≤ 2 * ((P6.m₀ + C7.m₁ : ℕ) : ℝ) * ((F.sf.β k)⁻¹) ^ 2 * Real.exp P6.κ := by
    have : 0 ≤ (F.sf.β k)⁻¹ := inv_nonneg.2 (by linarith)
    positivity
  intro ℓ _ hdvd
  refine torusClausesAt_add (hbox ℓ hdvd) ?_ hBbox hBR le_rfl le_rfl
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q ≠ 0 := by rintro rfl; exact NeZero.ne ℓ (by rw [hq, mul_zero])
  obtain ⟨m', hm'⟩ : ∃ m', m' = S.L ^ (kf - k) * q := ⟨_, rfl⟩
  obtain ⟨N₁, hN₁⟩ : ∃ N₁, N₁ = S.L ^ P6.m₀ * (S.L * m') := ⟨_, rfl⟩
  have hm'0 : m' ≠ 0 := by rw [hm']; exact mul_ne_zero (pow_ne_zero _ (NeZero.ne S.L)) hq0
  have : NeZero m' := ⟨hm'0⟩
  have : NeZero (S.L * m') := ⟨mul_ne_zero (NeZero.ne S.L) hm'0⟩
  have hN₁0 : N₁ ≠ 0 := by
    rw [hN₁]
    exact mul_ne_zero (pow_ne_zero _ (NeZero.ne S.L)) (mul_ne_zero (NeZero.ne S.L) hm'0)
  have : NeZero N₁ := ⟨hN₁0⟩
  have hℓ : ℓ = N₁ * S.L ^ C7.m₁ * S.L ^ k := by
    rw [hq, hN₁, hm', hM6]
    have e : S.L ^ (kf + 1) = S.L ^ k * S.L * S.L ^ (kf - k) := by
      rw [← pow_succ, ← pow_add]; congr 1; omega
    rw [e, pow_add]; ring
  subst hℓ
  have hlog : 0 ≤ (S.d : ℝ) * Real.log S.L :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hL0))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := torusClausesAt_rObs (P6 := P6) (sf := F.sf) hRt hBgR hεk hk1 hβ hv hunit hM6 hN₁
    (κR := κ + Real.log 2 + S.d * Real.log S.L + 1) (by linarith) (by linarith)
    (by convert hκf using 2; ring)
  rwa [show κ + Real.log 2 + S.d * Real.log S.L + 1 - S.d * Real.log S.L - 1 = κ + Real.log 2 by
    ring] at h


/-- The regrouping at the scale `k + 1` is a partition: `Σ_X p_{k+1}(X) = Σ_Y t(Y)`. -/
theorem sum_regroupFam_succ {d N : ℕ} (M L k : ℕ)
    (t : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (ℓ : ℕ) [NeZero ℓ]
    (g : Torus d ℓ → Fin N → ℂ) :
    ∑ X, regroupFam M L k t ℓ (k + 1) X g = ∑ Y, t ℓ Y g := by
  classical
  simp only [regroupFam_succ]
  unfold regroupAt
  exact Finset.sum_fiberwise _ _ _

/-- The constant of the box integral: `|det A| (2π)^{n/2} γ₁(box₁)^{|Λ|}`, positive for an invertible
whitening and a positive cutoff. -/
theorem whitenNorm_mul_box_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix (ι × Fin N) (ι × Fin N) ℝ} (hA : A.det ≠ 0) {p1 : ℝ} (hp1 : 0 < p1) :
    0 < whitenNorm A * (pdGaussian (Fin N) ℝ (gaussBox (Fin N) p1)).toReal ^ Fintype.card ι := by
  have h1 : 0 < whitenNorm A := by
    unfold whitenNorm
    have := abs_pos.2 hA
    positivity
  have h2 : 0 < (pdGaussian (Fin N) ℝ (gaussBox (Fin N) p1)).toReal := by
    have : IsProbabilityMeasure (pdGaussian (Fin N) ℝ) := ⟨pdGaussian_univ⟩
    exact ENNReal.toReal_pos (pdGaussian_gaussBox_pos hp1).ne' (measure_ne_top _ _)
  positivity

/-- **The box average of the fluctuation integrand of a member of the class at the stopping scale,
from the local form** (A6-3, gas layer; the generic core at a whitening `A` of each torus). Under the
local form on every torus of the family (`hW`, B1), the class data of the remainder terms (`hRt`,
`hBgR`, `hεk`, `hβ`), the numerical conditions of the cell gas and of the rates, the two-torus
closeness of the per-torus activities `lastSfAct` (`hC`, A2) and the amplitude condition `hamp` of
the conversion: there are activities `a` of Root-F's form at the scale `k + 1` (rate `κ`, amplitude
`c₉/2`) and constants `E` with, on every torus of the family and every source of the unit `ℓ¹` ball,
`ctxFluctBoxIntegralL = exp(E + Σ_X a(X; g))`. -/
theorem ctxFluctBoxIntegralL_eq_exp_of_boxLocalForm
    (F : RepFam S R k0 (kf + 1) M N geo cs P k C7.m₁ ϱ)
    (hM6 : M = S.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ kf + 1) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
    (A : ∀ (nK : ℕ) [NeZero nK], Matrix (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k × Fin N)
      (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k × Fin N) ℝ)
    (W : ∀ (nK : ℕ) [NeZero nK], Finset (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k) →
      (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k × Fin N → ℂ) →
      (GIdx S (sides S.L (kf + 1) nK) M (kf + 1) N → ℂ) → ℂ)
    (U : ∀ (nK : ℕ) [NeZero nK], Finset (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k) →
      (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k × Fin N → ℝ) → ℂ)
    {p1 G₀ Rt a ε εU : ℝ} {Mc : ℕ}
    (hW : ∀ (nK : ℕ) [NeZero nK], BoxLocalForm (F.ctx hM6 hkK nK) vc hv (A nK) p1 G₀ Rt Mc a ε εU
      (W nK) (U nK))
    (hRt : ∀ (N₁ : ℕ) [NeZero N₁],
      RTermsH4 (ϱ := ϱ) P6 F.sf.β F.sf.ν F.sf.a N₁ (F.sf.Rt N₁) fun _ => 1)
    (hBgR : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (F.sf.a k))
      (Def6.bgMass S.L k (F.sf.β k) (F.sf.ν k)))
    (hεk : 0 < P6.eps S.d S.L k) (hβ : 1 ≤ F.sf.β k) (hd : 0 < S.d) (hk1 : 1 ≤ k) (hk : k ≤ kf)
    (hs4 : 4 ≤ M * S.L ^ (k + 1)) (hMc : 0 < Mc) (hMcL : Mc ≤ M * S.L) (hp1 : 0 < p1)
    {κ c₉ δ κg : ℝ} (hκ : 0 < κ) (hκg : 0 ≤ κg) (ha : κg + 12 * S.d + 21 / 2 ≤ a)
    (hrate : κ + Real.log 2 ≤ κg / 3 ^ S.d - 1)
    (hε : ((2 * Mc : ℕ) : ℝ) ^ S.d * (ε + εU) ≤ 1 / 2)
    (hκf : Fluctuation.c1 S.d S.L * (κ + Real.log 2 + S.d * Real.log S.L + 2) ≤ P6.κ)
    {aC lam : ℝ} {t₀ : ℕ} (haC : 0 ≤ aC) (hlam : κ + Real.log 2 ≤ lam)
    (hC : LastScaleTwoTorusClose S.d N S.L M kf k (κ + Real.log 2) aC lam t₀
      (lastSfAct W U Mc p1 F.sf P6.m₀ hv))
    (hamp : (boxAmp S.d M S.L Mc (ε + εU) Rt +
        2 * ((P6.m₀ + C7.m₁ : ℕ) : ℝ) * ((F.sf.β k)⁻¹) ^ 2 * Real.exp P6.κ) +
      aC * Real.exp (κ + Real.log 2) +
      2 * (boxAmp S.d M S.L Mc (ε + εU) Rt +
        2 * ((P6.m₀ + C7.m₁ : ℕ) : ℝ) * ((F.sf.β k)⁻¹) ^ 2 * Real.exp P6.κ) *
        Real.exp ((κ + Real.log 2) * (t₀ : ℝ)) ≤
      c₉ / 2 * (S.L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((S.d : ℝ) - 2) / 2 + δ)))) :
    ∃ (aa : (ℓ : ℕ) → ℕ → Finset (Torus S.d ℓ) → (Torus S.d ℓ → Fin N → ℂ) → ℂ) (E : ℕ → ℂ),
      ObservableActivitiesAt S.d N S.L M κ c₉ δ (k + 1) kf aa ∧
      ∀ (nK : ℕ) [NeZero nK] (g : GIdx S (sides S.L (kf + 1) nK) M (kf + 1) N → ℂ),
        g ∈ LargeField.l1Ball _ →
        ctxFluctBoxIntegralL (F.ctx hM6 hkK nK) vc hv (A nK) p1 g =
          Complex.exp (E nK + ∑ X, aa (M * sides S.L (kf + 1) nK (kf + 1) * S.L ^ (kf + 1))
            (k + 1) X (fun x i => g (x, i))) := by
  classical
  have hT := lastScaleTorusClauses_lastSfAct F hM6 hkK vc hv hunit A W U hW hRt hBgR hεk hβ hk1 hk
    hMc hMcL hp1 hκ hκg ha hrate hε hκf
  have hB0 : 0 ≤ boxAmp S.d M S.L Mc (ε + εU) Rt +
      2 * ((P6.m₀ + C7.m₁ : ℕ) : ℝ) * ((F.sf.β k)⁻¹) ^ 2 * Real.exp P6.κ := by
    have : NeZero 1 := ⟨one_ne_zero⟩
    have h1 := boxAmp_nonneg (hW 1) hMc hp1 hκg ha hε
    have : 0 ≤ (F.sf.β k)⁻¹ := inv_nonneg.2 (by linarith)
    positivity
  obtain ⟨aa, haa, hsum⟩ := observableActivitiesAt_of_twoTorusClose hd hk hs4 hB0 haC hκ.le le_rfl
    hlam hamp (lastSfAct W U Mc p1 F.sf P6.m₀ hv) hT hC
  have hL0 : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hML : 0 < M * S.L ^ (kf + 1) := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne M)) (pow_pos hL0 _)
  have hgas : ∀ (nK : ℕ) [NeZero nK], ∃ E₀ : ℂ,
      ∀ g ∈ l1Ball (GIdx S (sides S.L (kf + 1) nK) M (kf + 1) N),
        ctxFluctBoxIntegralL (F.ctx hM6 hkK nK) vc hv (A nK) p1 g =
          (whitenNorm (A nK) : ℂ) *
            Complex.exp (E₀ + (F.ctx hM6 hkK nK).Rres Set.univ (fun _ => hv) hv g) *
            (((pdGaussian (Fin N) ℝ (gaussBox (Fin N) p1)).toReal ^
              Fintype.card (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k) : ℝ) : ℂ) *
            Complex.exp (∑ 𝒳, boxCellAct (W nK) (U nK) Mc p1 g 𝒳) :=
    fun nK _ => ctxFluctBoxIntegralL_eq_boxGas (hW nK) hMc hp1 hκg ha hε
  let E : ℕ → ℂ := fun nK => if h : nK ≠ 0 then
    (haveI : NeZero nK := ⟨h⟩
    ((Real.log (whitenNorm (A nK) * (pdGaussian (Fin N) ℝ (gaussBox (Fin N) p1)).toReal ^
        Fintype.card (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k)) : ℝ) : ℂ) +
      Classical.choose (hgas nK) +
      ∑ X, lastSfAct W U Mc p1 F.sf P6.m₀ hv (M * sides S.L (kf + 1) nK (kf + 1) * S.L ^ (kf + 1))
        X 0) else 0
  refine ⟨aa, E, haa, fun nK _ g hg => ?_⟩
  have hspec := Classical.choose_spec (hgas nK) g hg
  set E₀ := Classical.choose (hgas nK) with hE₀
  set ℓ := M * sides S.L (kf + 1) nK (kf + 1) * S.L ^ (kf + 1) with hℓ
  have hdvd : M * S.L ^ (kf + 1) ∣ ℓ := ⟨nK, side_eq_mul M S.L (kf + 1) nK⟩
  set g' : Torus S.d ℓ → Fin N → ℂ := fun x i => g (x, i) with hg'
  have hsg : srcIdx (S := S) (n := sides S.L (kf + 1) nK) (M := M) (K := kf + 1) g' = g := rfl
  have hbox : ∑ 𝒳, boxCellAct (W nK) (U nK) Mc p1 g 𝒳 =
      ∑ X, torusFam M S.L (kf + 1) (fun nK _ => boxAct (W nK) (U nK) Mc p1) ℓ X g' := by
    rw [← hsg, ← sum_boxAct]
    refine Finset.sum_congr rfl fun X _ => ?_
    rw [torusFam_apply hML]
  have hR : (F.ctx hM6 hkK nK).Rres Set.univ (fun _ => hv) hv g =
      ∑ X, regroupFam M S.L k (fun ℓ => rObs F.sf P6.m₀ hv ℓ) ℓ (k + 1) X g' := by
    rw [sum_regroupFam_succ, ← sum_rObs_eq_Rres (F.ctx hM6 hkK nK) hv hk1 g]
    rfl
  have hlast : (∑ 𝒳, boxCellAct (W nK) (U nK) Mc p1 g 𝒳) +
      (F.ctx hM6 hkK nK).Rres Set.univ (fun _ => hv) hv g =
      ∑ X, lastSfAct W U Mc p1 F.sf P6.m₀ hv ℓ X g' := by
    rw [hbox, hR, ← Finset.sum_add_distrib]
    rfl
  have hsplit : ∑ X, lastSfAct W U Mc p1 F.sf P6.m₀ hv ℓ X g' =
      ∑ X, lastSfAct W U Mc p1 F.sf P6.m₀ hv ℓ X 0 + ∑ X, aa ℓ (k + 1) X g' := by
    rw [hsum ℓ hdvd g', ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun X _ => by ring
  have hpos := whitenNorm_mul_box_pos (ι := BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k)
    (hW nK).det_ne_zero hp1
  have hc : ((whitenNorm (A nK) : ℝ) : ℂ) * (((pdGaussian (Fin N) ℝ (gaussBox (Fin N) p1)).toReal ^
      Fintype.card (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k) : ℝ) : ℂ) =
      Complex.exp ((Real.log (whitenNorm (A nK) * (pdGaussian (Fin N) ℝ
        (gaussBox (Fin N) p1)).toReal ^ Fintype.card (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k))
          : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hpos]
    push_cast; ring
  have hE : E nK = ((Real.log (whitenNorm (A nK) * (pdGaussian (Fin N) ℝ (gaussBox (Fin N) p1)).toReal ^
        Fintype.card (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k)) : ℝ) : ℂ) + E₀ +
      ∑ X, lastSfAct W U Mc p1 F.sf P6.m₀ hv ℓ X 0 := by
    simp only [E, ne_eq, NeZero.ne nK, not_false_eq_true, ↓reduceDIte]
    rfl
  rw [hspec, hE]
  calc (whitenNorm (A nK) : ℂ) * Complex.exp (E₀ + (F.ctx hM6 hkK nK).Rres Set.univ (fun _ => hv) hv g) *
        (((pdGaussian (Fin N) ℝ (gaussBox (Fin N) p1)).toReal ^
          Fintype.card (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k) : ℝ) : ℂ) *
        Complex.exp (∑ 𝒳, boxCellAct (W nK) (U nK) Mc p1 g 𝒳)
      = (((whitenNorm (A nK) : ℝ) : ℂ) * (((pdGaussian (Fin N) ℝ (gaussBox (Fin N) p1)).toReal ^
          Fintype.card (BlockAt S (sides S.L (kf + 1) nK) M (kf + 1) k) : ℝ) : ℂ)) *
        Complex.exp (E₀ + ((∑ 𝒳, boxCellAct (W nK) (U nK) Mc p1 g 𝒳) +
          (F.ctx hM6 hkK nK).Rres Set.univ (fun _ => hv) hv g)) := by
        simp only [Complex.exp_add]
        ring
    _ = _ := by
        rw [hc, hlast, hsplit, ← Complex.exp_add]
        congr 1
        ring

end Last



section Exact

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- **The box integral at the exact whitening is the Gaussian average of `sfGaussIntegrand`**:
`ctxBoxIntegral = Z_K ∫_{box} sfGaussIntegrand dγ` for `K = β_k D` positive definite. -/
theorem ctxBoxIntegral_eq_gauss (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) (hK : (sfFinalK C hv).PosDef) (p1 : ℝ)
    (g : GIdx S n M K N → ℂ) :
    ctxBoxIntegral C vc hv p1 g =
      (pdGaussNorm (BlockAt S n M K k × Fin N) ℝ (sfFinalK C hv) : ℂ) *
        ∫ w in gaussBox (BlockAt S n M K k × Fin N) p1,
          sfGaussIntegrand C vc Set.univ hv g (sfFinalK C hv) (fun _ => hv) w
          ∂(pdGaussian (BlockAt S n M K k × Fin N) ℝ) := by
  unfold ctxBoxIntegral ctxBoxIntegralL
  rw [whitenNorm_pdSqrtInv hK]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  beta_reduce
  rw [mismatchFactor_pdSqrtInv hK]
  simp [sfGaussIntegrand]

end Exact

section Amp

/-- **The amplitude condition of the last-scale conversion from `β₀`** (A6-3 (e); the numerical
condition of the parity gain). With `θ = (d-2)/2 + δ` and `T = 1 + 2 e^{κ' t₀}`: if the box amplitude
is at most `D β_k^{-p}` with `θ ≤ p (d - 2)` (in the source `p = 1 - 2α`, from `ε/R_t² ≈ β_k^{-1} p₁²`
and the cutoff `p₁ ≈ β_k^{α}`, so the condition is `δ ≤ (d-2)(1/2 - 2α)`), the remainder amplitude is at
most `C_R β_k^{-2}`, the closeness amplitude satisfies `a_C e^{κ'} ≤ (c₉/4) L^{-(k+1)θ}`, and `β₀` is so
large that `L^θ ≤ (c₉/8)/(D T + 1) β₀^p` and `L^θ ≤ (c₉/8)/(C_R T + 1) β₀²`, then the amplitude
condition `hamp` of `observableActivitiesAt_of_twoTorusClose` holds. -/
theorem lastScaleAmp_of_beta {d L k : ℕ} {β0 c₉ δ p D CR κ' aC Bbox BR : ℝ} {t₀ : ℕ}
    (hd : 3 ≤ d) (hL : 2 ≤ L) (hc : 0 < c₉) (hD : 0 ≤ D) (hCR : 0 ≤ CR) (hβ0 : 0 < β0)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ ((d : ℝ) - 2) / 2) (hpδ : ((d : ℝ) - 2) / 2 + δ ≤ p * ((d : ℝ) - 2))
    (hBbox : Bbox ≤ D * ((Balaban.LargeField.ActionConv.betaK d L k β0) ^ p)⁻¹)
    (hBR : BR ≤ CR * ((Balaban.LargeField.ActionConv.betaK d L k β0) ^ 2)⁻¹)
    (haC : aC * Real.exp κ' ≤ c₉ / 4 * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))))
    (hβp : (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) ≤
      c₉ / 8 / (D * (1 + 2 * Real.exp (κ' * (t₀ : ℝ))) + 1) * β0 ^ p)
    (hβ2 : (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) ≤
      c₉ / 8 / (CR * (1 + 2 * Real.exp (κ' * (t₀ : ℝ))) + 1) * β0 ^ 2) :
    (Bbox + BR) + aC * Real.exp κ' + 2 * (Bbox + BR) * Real.exp (κ' * (t₀ : ℝ)) ≤
      c₉ / 2 * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
  set T : ℝ := 1 + 2 * Real.exp (κ' * (t₀ : ℝ)) with hT
  set Λ : ℝ := (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) with hΛ
  have hT0 : 0 < T := by positivity
  have hΛ0 : 0 ≤ Λ := Real.rpow_nonneg (by positivity) _
  have hDT : 0 ≤ D * T := mul_nonneg hD hT0.le
  have h1 := betaK_inv_rpow_le (d := d) (L := L) (k := k) (c₉ := c₉ / 8 / (D * T + 1)) (p := p)
    hd hL (by positivity) hβ0 hpδ hβp
  have hbox : T * Bbox ≤ c₉ / 8 * Λ := by
    calc T * Bbox ≤ T * (D * ((Balaban.LargeField.ActionConv.betaK d L k β0) ^ p)⁻¹) :=
          mul_le_mul_of_nonneg_left hBbox hT0.le
      _ = (D * T) * ((Balaban.LargeField.ActionConv.betaK d L k β0) ^ p)⁻¹ := by ring
      _ ≤ (D * T) * (c₉ / 8 / (D * T + 1) * Λ) := mul_le_mul_of_nonneg_left h1 hDT
      _ = (D * T / (D * T + 1)) * (c₉ / 8 * Λ) := by field_simp
      _ ≤ 1 * (c₉ / 8 * Λ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_one (by linarith)]; linarith
      _ = c₉ / 8 * Λ := one_mul _
  have hR : (CR * T) * ((Balaban.LargeField.ActionConv.betaK d L k β0) ^ 2)⁻¹ ≤ c₉ / 8 * Λ :=
    rest_small_in_beta hd hL (by positivity) (mul_nonneg hCR hT0.le) hβ0 hδ0 hδ hβ2
  have hRT : T * BR ≤ c₉ / 8 * Λ := by
    calc T * BR ≤ T * (CR * ((Balaban.LargeField.ActionConv.betaK d L k β0) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hBR hT0.le
      _ = (CR * T) * ((Balaban.LargeField.ActionConv.betaK d L k β0) ^ 2)⁻¹ := by ring
      _ ≤ _ := hR
  calc (Bbox + BR) + aC * Real.exp κ' + 2 * (Bbox + BR) * Real.exp (κ' * (t₀ : ℝ))
      = T * Bbox + T * BR + aC * Real.exp κ' := by rw [hT]; ring
    _ ≤ c₉ / 8 * Λ + c₉ / 8 * Λ + c₉ / 4 * Λ := add_le_add (add_le_add hbox hRT) haC
    _ ≤ c₉ / 2 * Λ := by nlinarith


/-- **The rate tie of the remainder activities from the prefix tie**: for `L ≥ 3` and `κ > 0`,
`c₁ (κ + log 2 + d log L + 2) ≤ 3^{d+1} L^{2d+1} (κ + 1)`, so the tie
`3^{d+1} L^{2d+1} (κ + 1) ≤ κ_flow` of `PrefixInput` gives the hypothesis `hκf` of
`lastScaleTorusClauses_lastSfAct` (`c₁ = (3(2L-1))^d ≤ (6L)^d`, and
`log 2 + d log L + 2 ≤ 3L + 3dL/2 ≤ 3L(L/2)^d`). -/
theorem c1_mul_rate_le {d L : ℕ} (hL : 3 ≤ L) {κ : ℝ} (hκ : 0 < κ) :
    Fluctuation.c1 d L * (κ + Real.log 2 + d * Real.log L + 2) ≤
      (3 : ℝ) ^ (d + 1) * (L : ℝ) ^ (2 * d + 1) * (κ + 1) := by
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hc1 : Fluctuation.c1 d L ≤ (6 * (L : ℝ)) ^ d := by
    unfold Fluctuation.c1
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have : ((3 * (2 * L - 1) : ℕ) : ℝ) ≤ 6 * L := by
      have h1 : 3 * (2 * L - 1) ≤ 6 * L := by omega
      exact_mod_cast h1
    exact this
  have hlogL : Real.log L ≤ L := by linarith [Real.log_le_sub_one_of_pos hL0]
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hbern : 1 + (d : ℝ) * (1 / 2) ≤ (1 + 1 / 2) ^ d :=
    one_add_mul_le_pow (by norm_num) d
  have hpow : ((3 : ℝ) / 2) ^ d ≤ ((L : ℝ) / 2) ^ d :=
    pow_le_pow_left₀ (by norm_num) (by linarith) d
  have hX : Real.log 2 + d * Real.log L + 2 ≤ 3 * L * ((L : ℝ) / 2) ^ d := by
    have h1 : (d : ℝ) * Real.log L ≤ d * L := mul_le_mul_of_nonneg_left hlogL (Nat.cast_nonneg d)
    have h2 : 3 * (L : ℝ) * (1 + d * (1 / 2)) ≤ 3 * L * ((L : ℝ) / 2) ^ d := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc 1 + (d : ℝ) * (1 / 2) ≤ (1 + 1 / 2) ^ d := hbern
        _ = ((3 : ℝ) / 2) ^ d := by norm_num
        _ ≤ ((L : ℝ) / 2) ^ d := hpow
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hsplit : (3 : ℝ) ^ (d + 1) * (L : ℝ) ^ (2 * d + 1) =
      (6 * (L : ℝ)) ^ d * (3 * L * ((L : ℝ) / 2) ^ d) := by
    rw [mul_pow, div_pow, pow_succ, show 2 * d + 1 = d + d + 1 by ring, pow_succ, pow_add]
    field_simp
    rw [show (6 : ℝ) ^ d = 2 ^ d * 3 ^ d by rw [← mul_pow]; norm_num]
    ring
  have hY : 1 ≤ 3 * (L : ℝ) * ((L : ℝ) / 2) ^ d := by
    have : (1 : ℝ) ≤ ((L : ℝ) / 2) ^ d := one_le_pow₀ (by linarith)
    nlinarith
  have hc1n : 0 ≤ Fluctuation.c1 d L := by unfold Fluctuation.c1; positivity
  have hlogn : 0 ≤ Real.log 2 + d * Real.log L + 2 := by
    have : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by linarith)
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  calc Fluctuation.c1 d L * (κ + Real.log 2 + d * Real.log L + 2)
      ≤ (6 * (L : ℝ)) ^ d * (κ + Real.log 2 + d * Real.log L + 2) :=
        mul_le_mul_of_nonneg_right hc1 (by linarith)
    _ ≤ (6 * (L : ℝ)) ^ d * ((3 * L * ((L : ℝ) / 2) ^ d) * (κ + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith
    _ = _ := by rw [hsplit]; ring

end Amp

end Balaban.RootFSpine
