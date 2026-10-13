/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2Regime
public import Balaban.Background.Contraction
public import Balaban.Fluctuation.CovSqrtSupComplex
public import Balaban.Fluctuation.CovarianceSup
public import Balaban.Localization.CompWeightAdmissible
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Scale-uniform inputs of the fluctuation step

Two of the scale-dependent inputs of the general-scale fluctuation step, both pure arithmetic.
The general-scale step setting, its cover geometry and the radius tower are separate packages.

**Mass.** For `ν_k` the running mass at scale `k` and `ν = ν_k L^{-2k}` the physical mass,
`ν (L^{k+1})² = L² ν_k`, so the mass premise `ν (L^{k+1})² ≤ 1` of the background solver is
exactly `ν_k ≤ L^{-2}`. For `k ≤ k₀` the running relations give `b_k ν_k ≤ e^{2ε}` and
`b_k ≥ β e^{-ε}`, hence `ν_k ≤ e^{3ε}/β`, and `β ≥ L² e^{3ε}` suffices at every such scale. Above
`k₀` only a lower bound on `b_k ν_k` is available; if `ν_k > L^{-2}` the premise fails. Massive
backgrounds above that range are a separate package.

**Weight.** The covariance constants depend on the scale only through the weight `a_k`, which stays
in `[1/2, 2]`. We give explicit maxima over that interval.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Localization Balaban.SmallField.Def6v2 Balaban.LargeField

/-! ### T1: the mass premise -/

/-- `ν (L^{k+1})² = L² ν_k` for the physical mass `ν = ν_k L^{-2k}`. -/
theorem sfBgMassAt_mul_sq {L : ℕ} [NeZero L] (k : ℕ) (νk : ℝ) :
    sfBgMassAt L k νk * ((L : ℝ) ^ (k + 1)) ^ 2 = (L : ℝ) ^ 2 * νk := by
  have h := physMass_mul_sq (L := L) k νk
  unfold sfBgMassAt
  calc physMass L k νk * ((L : ℝ) ^ (k + 1)) ^ 2
      = (L : ℝ) ^ 2 * (physMass L k νk * ((L : ℝ) ^ k) ^ 2) := by ring
    _ = _ := by rw [h]

/-- The mass premise of the background solver at index `k+1` is exactly `ν_k ≤ L^{-2}`. -/
theorem massLe_iff {L : ℕ} [NeZero L] (k : ℕ) (νk : ℝ) :
    sfBgMassAt L k νk * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1 ↔ νk ≤ ((L : ℝ) ^ 2)⁻¹ := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hp : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  rw [sfBgMassAt_mul_sq, inv_eq_one_div, le_div_iff₀ hp]
  constructor <;> intro h <;> linarith

/-- **Early scales.** Under the running relations with a genuine `k₀`, for `L ≥ 2`, every scale
`k ≤ k₀` and `β ≥ L² e^{3ε}`, the running mass satisfies `ν_k ≤ L^{-2}`; equivalently the mass
premise `ν (L^{k+1})² ≤ 1` holds for the physical mass `ν = ν_k L^{-2k}`. -/
theorem nu_le_of_early {d L : ℕ} {β ν a ε : ℝ} {b n : ℕ → ℝ}
    (h : RunningHyp d L β ν a ε b n) (hg : KZeroGenuine β ν)
    (hβ : (L : ℝ) ^ 2 * Real.exp (3 * ε) ≤ β) {k : ℕ} (hk : k ≤ kZero d L β ν) :
    n k ≤ ((L : ℝ) ^ 2)⁻¹ := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by have := h.hL; omega : 0 < L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := h.hL; omega : 1 ≤ L)
  obtain ⟨γ, hγ, hlγ, hb⟩ := h.beta_eq k
  obtain ⟨δ, hδ, -, hn⟩ := h.nu_eq k
  have hn0 : 0 < n k := by rw [hn]; have := h.hν; positivity
  have hγe := exp_neg_le_of_abs_log hγ hlγ
  have hbk : β * Real.exp (-ε) ≤ b k := by
    rw [hb]
    have h1 : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
    have hβ0 := h.hβ
    calc β * Real.exp (-ε) = β * 1 * Real.exp (-ε) := by ring
      _ ≤ β * (L : ℝ) ^ (k * (d - 2)) * γ :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hβ0.le) hγe (Real.exp_pos _).le (by positivity)
  have hprod := h.beta_mul_nu_le hg hk
  have h2 : β * Real.exp (-ε) * n k ≤ Real.exp (2 * ε) :=
    (mul_le_mul_of_nonneg_right hbk hn0.le).trans hprod
  have he : Real.exp (-ε) * Real.exp (3 * ε) = Real.exp (2 * ε) := by
    rw [← Real.exp_add]; ring_nf
  have hep := Real.exp_pos (-ε)
  rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
  have h3 : (L : ℝ) ^ 2 * Real.exp (3 * ε) * Real.exp (-ε) * n k ≤ β * Real.exp (-ε) * n k := by
    gcongr
  have h4 : Real.exp (2 * ε) * ((L : ℝ) ^ 2 * n k) ≤ Real.exp (2 * ε) * 1 := by
    calc Real.exp (2 * ε) * ((L : ℝ) ^ 2 * n k)
        = (L : ℝ) ^ 2 * Real.exp (3 * ε) * Real.exp (-ε) * n k := by rw [← he]; ring
      _ ≤ _ := h3
      _ ≤ _ := h2
      _ = _ := (mul_one _).symm
  have h5 := le_of_mul_le_mul_left h4 (Real.exp_pos _)
  linarith

/-- **Theorem `massLe_of_early`.** For `L ≥ 2`, under `RunningHyp` and `KZeroGenuine`, `β ≥ L² e^{3ε}`
and `k ≤ k₀`, the mass premise `ν (L^{k+1})² ≤ 1` of `BgHyp d L (k+1)` holds for the physical mass
`ν = ν_k L^{-2k}` of the running coefficient `n k`. -/
theorem massLe_of_early {d L : ℕ} [NeZero L] {β ν a ε : ℝ} {b n : ℕ → ℝ}
    (h : RunningHyp d L β ν a ε b n) (hg : KZeroGenuine β ν)
    (hβ : (L : ℝ) ^ 2 * Real.exp (3 * ε) ≤ β) {k : ℕ} (hk : k ≤ kZero d L β ν) :
    sfBgMassAt L k (n k) * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1 :=
  (massLe_iff k (n k)).2 (nu_le_of_early h hg hβ hk)

/-! ### T2: above the range -/

/-- If `ν_k > L^{-2}` the mass premise fails for the physical mass. -/
theorem not_massLe_of_gt {L : ℕ} [NeZero L] (k : ℕ) {νk : ℝ} (h : ((L : ℝ) ^ 2)⁻¹ < νk) :
    ¬ sfBgMassAt L k νk * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1 :=
  fun hle => absurd ((massLe_iff k νk).1 hle) (not_le.2 h)

/-- Above `k₀` the running mass is bounded below: `ν_j > e^{-2ε} / b_j`
(from `lt_beta_mul_nu`); this is the range in which `ν_j > L^{-2}` can occur. -/
theorem nu_gt_of_gt_kZero {d L : ℕ} {β ν a ε : ℝ} {b n : ℕ → ℝ}
    (h : RunningHyp d L β ν a ε b n) {j : ℕ} (hj : kZero d L β ν < j) :
    Real.exp (-(2 * ε)) / b j < n j := by
  obtain ⟨γ, hγ, -, hb⟩ := h.beta_eq j
  have hbj : 0 < b j := by rw [hb]; have := h.hβ; have : (0:ℝ) < L := by
                                         exact_mod_cast (by have := h.hL; omega : 0 < L)
                           positivity
  rw [div_lt_iff₀ hbj]
  have := h.lt_beta_mul_nu hj
  linarith [mul_comm (b j) (n j)]

/-! ### T4: non-vacuity -/

/-- Explicit regime instance of `massLe_of_early`: for `d ≥ 2`, `L ≥ 2`, `ε = 0`, `β = L²`,
`ν = 1/(β L^d)`, there are exact running coefficients with `1 ≤ k₀` genuine, and the mass premise
holds at scale `k = 1`. -/
theorem massLe_of_early_nonempty {d L : ℕ} [NeZero L] (hd : 2 ≤ d) (hL : 2 ≤ L) :
    ∃ (β ν : ℝ) (b n : ℕ → ℝ), RunningHyp d L β ν (5 / 4) 0 b n ∧ KZeroGenuine β ν ∧
      (L : ℝ) ^ 2 * Real.exp (3 * 0) ≤ β ∧ 1 ≤ kZero d L β ν ∧
      sfBgMassAt L 1 (n 1) * ((L : ℝ) ^ (1 + 1)) ^ 2 ≤ 1 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  set β : ℝ := (L : ℝ) ^ 2 with hβdef
  have hβ : 0 < β := by positivity
  set ν : ℝ := 1 / (β * (L : ℝ) ^ d) with hνdef
  have hν : 0 < ν := by positivity
  have h : RunningHyp d L β ν (5 / 4) 0 (fun k => β * (L : ℝ) ^ (k * (d - 2)) * 1)
      (fun k => ν * (L : ℝ) ^ (2 * k) * 1) :=
    { hd := hd, hL := hL, hβ := hβ, hν := hν, ha1 := by norm_num, ha2 := by norm_num
      hε0 := le_rfl, hε := by norm_num
      beta_eq := fun k => ⟨1, one_pos, by simp, rfl⟩
      nu_eq := fun k => ⟨1, one_pos, by simp, rfl⟩ }
  have hβν : β * ν = 1 / (L : ℝ) ^ d := by rw [hνdef]; field_simp
  have hg : KZeroGenuine β ν := by
    unfold KZeroGenuine
    rw [hβν, div_le_one (by positivity)]
    exact one_le_pow₀ hL1
  have hk : 1 ≤ kZero d L β ν := by
    unfold kZero
    refine le_csSup (kZero_bddAbove (by omega) hL (mul_pos hβ hν)) ?_
    show β * ν * (L : ℝ) ^ (1 * d) ≤ 1
    rw [hβν, one_mul]
    have : (0 : ℝ) < (L : ℝ) ^ d := by positivity
    rw [one_div, inv_mul_cancel₀ this.ne']
  have hth : (L : ℝ) ^ 2 * Real.exp (3 * 0) ≤ β := by simp [hβdef]
  exact ⟨β, ν, _, _, h, hg, hth, hk, massLe_of_early h hg hth hk⟩

/-- The landed witness step has `ν = 1/81` at `k = 1`, `L = 3`: this is exactly the boundary
`ν_1 = L^{-2}`, where the mass premise holds with equality. -/
theorem witness_mass_boundary :
    sfBgMassAt 3 1 (1 / 9 : ℝ) = 1 / 81 ∧
    sfBgMassAt 3 1 (1 / 9 : ℝ) * (((3 : ℕ) : ℝ) ^ (1 + 1)) ^ 2 = 1 ∧
    (1 / 9 : ℝ) = (((3 : ℕ) : ℝ) ^ 2)⁻¹ := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [sfBgMassAt, physMass]

/-- The value `1/81` of the witness step determines `ν_1 = 1/9 = L^{-2}`. -/
theorem witness_nu_eq {νk : ℝ} (h : sfBgMassAt 3 1 νk = 1 / 81) : νk = (((3 : ℕ) : ℝ) ^ 2)⁻¹ := by
  unfold sfBgMassAt physMass at h
  norm_num at h ⊢
  linarith

/-! ### T3: the weight -/

variable {d L N : ℕ}

/-- Maximum over `a ∈ [1/2, 2]` of the sup constant of `C^{1/2}` (real version). -/
noncomputable def covSupMax (d L N : ℕ) : ℝ :=
  N * Green.ballConst d (xAgmonRate d L / L) *
    (covDecayConst d L 2 (xAgmonRate d L) * Real.exp (xAgmonRate d L * d / L) * Real.sqrt 2)

/-- Maximum over `a ∈ [1/2, 2]` of the sup constant of `C^{1/2}(s)` (complex version). -/
noncomputable def covSupMaxC (d L N : ℕ) (κ : ℝ) : ℝ :=
  N * Green.ballConst d (xAgmonRate d L / L) *
    ((2 * Real.exp (xAgmonRate d L * (2 * d)) + 2 * covTConst d L 1 (xAgmonRate d L) κ) *
      Real.exp (xAgmonRate d L * d / L) * Real.sqrt 2)

/-- The constant `B₅` of `RayData`, uniform over the weights. -/
noncomputable def B5Max (d L N : ℕ) : ℝ := max 1 (Real.sqrt N * covSupMax d L N)

/-- The constant `K₂` of `RayData` (it does not depend on the weight). -/
noncomputable def K2Max (d L N : ℕ) [NeZero L] : ℝ :=
  max (max 1 (Balaban.Background.cK2 d L N)) (Real.sqrt N * Balaban.Background.cK2 d L N)

theorem inv_sqrt_le_sqrt_two {a : ℝ} (h : 1 / 2 ≤ a) : (Real.sqrt a)⁻¹ ≤ Real.sqrt 2 := by
  have ha : 0 < a := by linarith
  have h1 : 1 ≤ Real.sqrt 2 * Real.sqrt a := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.le_sqrt_of_sq_le
    linarith
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  calc (Real.sqrt a)⁻¹ = (Real.sqrt a)⁻¹ * 1 := by ring
    _ ≤ (Real.sqrt a)⁻¹ * (Real.sqrt 2 * Real.sqrt a) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hs.le)
    _ = Real.sqrt 2 := by field_simp

theorem ballConst_pos (hd : 0 < d) (hL : 3 ≤ L) : 0 < Green.ballConst d (xAgmonRate d L / L) := by
  have hr : 0 < xAgmonRate d L / L := by
    have := xAgmonRate_pos (L := L) hd hL
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  unfold Green.ballConst
  have h1 : Real.exp (-(xAgmonRate d L / L)) < 1 := by
    have := Real.exp_lt_exp.2 (show -(xAgmonRate d L / L) < 0 by linarith)
    simpa using this
  have h2 := Real.exp_pos (-(xAgmonRate d L / L))
  apply pow_pos
  apply div_pos <;> linarith

theorem covSupConst_le_covSupMax (hd : 0 < d) (hL : 3 ≤ L) {a : ℝ} (ha : a ∈ Set.Icc (1 / 2 : ℝ) 2) :
    covSupConst d L N a ≤ covSupMax d L N := by
  obtain ⟨h1, h2⟩ := ha
  have ha0 : 0 < a := by linarith
  have hB := ballConst_pos (d := d) hd hL
  unfold covSupConst covSupMax covSqrtEntryConst covDecayConst
  rw [div_eq_mul_inv]
  have hS : 0 ≤ Real.sqrt (92 * valConstX d) := Real.sqrt_nonneg _
  have hLn : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hD : 2 * Real.exp (2 * d * xAgmonRate d L) *
        (1 + 2 * a * (L : ℝ) ^ 2 * Real.sqrt (92 * valConstX d) *
          Real.exp (4 * d * xAgmonRate d L)) ≤
      2 * Real.exp (2 * d * xAgmonRate d L) *
        (1 + 2 * 2 * (L : ℝ) ^ 2 * Real.sqrt (92 * valConstX d) *
          Real.exp (4 * d * xAgmonRate d L)) := by
    gcongr
  have hE := Real.exp_pos (xAgmonRate d L * d / L)
  have hD0 : 0 ≤ 2 * Real.exp (2 * d * xAgmonRate d L) *
        (1 + 2 * a * (L : ℝ) ^ 2 * Real.sqrt (92 * valConstX d) *
          Real.exp (4 * d * xAgmonRate d L)) := by positivity
  gcongr
  exact mul_le_mul (mul_le_mul_of_nonneg_right hD hE.le) (inv_sqrt_le_sqrt_two h1)
    (inv_nonneg.2 (Real.sqrt_nonneg _)) (by positivity)

theorem covSupConstC_nonneg (hd : 0 < d) (hL : 3 ≤ L) {a : ℝ} (ha : 0 < a) (κ : ℝ) :
    0 ≤ covSupConstC d L N a κ := by
  have hB := ballConst_pos (d := d) hd hL
  have := covC1Const_nonneg d L ha (xAgmonRate d L) κ
  unfold covSupConstC covSqrtEntryConstC
  positivity

theorem covSupConstC_le_covSupMaxC (hd : 0 < d) (hL : 3 ≤ L) (κ : ℝ) {a : ℝ}
    (ha : a ∈ Set.Icc (1 / 2 : ℝ) 2) : covSupConstC d L N a κ ≤ covSupMaxC d L N κ := by
  obtain ⟨h1, h2⟩ := ha
  have ha0 : 0 < a := by linarith
  have hB := ballConst_pos (d := d) hd hL
  have hT : covTConst d L a (xAgmonRate d L) κ = a ^ 2 * covTConst d L 1 (xAgmonRate d L) κ := by
    unfold covTConst; ring
  have hT0 := covTConst_nonneg d L 1 (xAgmonRate d L) κ
  have hC : covC1Const d L a (xAgmonRate d L) κ ≤
      2 * Real.exp (xAgmonRate d L * (2 * d)) + 2 * covTConst d L 1 (xAgmonRate d L) κ := by
    unfold covC1Const
    rw [hT]
    have : a ^ 2 * covTConst d L 1 (xAgmonRate d L) κ / a =
        a * covTConst d L 1 (xAgmonRate d L) κ := by field_simp
    rw [this]
    nlinarith
  have hC0 := covC1Const_nonneg d L ha0 (xAgmonRate d L) κ
  have hE := Real.exp_pos (xAgmonRate d L * d / L)
  unfold covSupConstC covSupMaxC covSqrtEntryConstC
  rw [div_eq_mul_inv]
  gcongr
  exact mul_le_mul (mul_le_mul_of_nonneg_right hC hE.le) (inv_sqrt_le_sqrt_two h1)
    (inv_nonneg.2 (Real.sqrt_nonneg _)) (by positivity)

/-- `B₅` of `RayData`: for every weight in `[1/2, 2]` the required lower bound holds with `B5Max`. -/
theorem B5_le_B5Max (hd : 0 < d) (hL : 3 ≤ L) {a : ℝ} (ha : a ∈ Set.Icc (1 / 2 : ℝ) 2) :
    max 1 (Real.sqrt N * covSupConst d L N a) ≤ B5Max d L N := by
  unfold B5Max
  exact max_le_max le_rfl
    (mul_le_mul_of_nonneg_left (covSupConst_le_covSupMax hd hL ha) (Real.sqrt_nonneg _))

/-- `K₂` of `RayData` does not depend on the weight; `K2Max` is the least admissible value. -/
theorem K2_le_K2Max [NeZero L] : max (max 1 (Balaban.Background.cK2 d L N))
    (Real.sqrt N * Balaban.Background.cK2 d L N) ≤ K2Max d L N := le_rfl

/-- Positivity and bounds of `|C| + 1` (the divisor of the radius tower `towerCpsi`). -/
theorem abs_covSupConstC_add_one_bounds (hd : 0 < d) (hL : 3 ≤ L) (κ : ℝ) {a : ℝ}
    (ha : a ∈ Set.Icc (1 / 2 : ℝ) 2) :
    1 ≤ |covSupConstC d L N a κ| + 1 ∧
      |covSupConstC d L N a κ| + 1 ≤ covSupMaxC d L N κ + 1 := by
  have h0 := covSupConstC_nonneg (N := N) hd hL (by linarith [ha.1] : 0 < a) κ
  have h1 := covSupConstC_le_covSupMaxC (N := N) hd hL κ ha
  rw [abs_of_nonneg h0]
  constructor <;> linarith

/-- The weight of the composed background at every scale `r ≥ 1` lies in `[1/2, 2]`, so all of the
bounds above hold at every scale. -/
theorem covSupConstC_compWeight_le (hd : 0 < d) (hL : 3 ≤ L) (κ : ℝ) {a₁ : ℝ}
    (h1 : 9 / 16 ≤ a₁) (h2 : a₁ ≤ 2) {r : ℕ} (hr : 1 ≤ r) :
    covSupConstC d L N (Balaban.Background.compWeight L a₁ r) κ ≤ covSupMaxC d L N κ ∧
    covSupConst d L N (Balaban.Background.compWeight L a₁ r) ≤ covSupMax d L N :=
  have ha := Balaban.Background.compWeight_mem_Icc hL h1 h2 hr
  ⟨covSupConstC_le_covSupMaxC hd hL κ ha, covSupConst_le_covSupMax hd hL ha⟩

end Balaban.Fluctuation
