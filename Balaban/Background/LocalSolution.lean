/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Data
public import Balaban.Background.ConstantConfig
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The local complex solution (LEMMA53-astra.md, §1 and §6, item 4)

For a block with data `Ψ_B`, `H_B ∈ ℂ^N`, weight `a` and mass `ν`, the explicit solution of the
local bilinear problem is `φ^B = cMinimizer a ν Ψ_B H_B` with multiplier
`α̂^B = cMultiplier a ν Ψ_B H_B`.  This file proves the quantitative estimates (2) of the note,
with constants `500` and `128` in place of `1695` and `272` (the constants of the note are not
needed; only that they are absolute).

* `local_solution`: the estimates from three abstract hypotheses on `(Ψ, H, a, ν)`;
* `site_Ψ_hyp`, `site_H_hyp`: the three hypotheses from the data conditions (R1)-(R4), (C1)-(C3).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {N : ℕ}

theorem vn_eq_cNorm (v : Fin N → ℂ) : vn v = cNorm v := rfl

/-- The local estimates: the complex solution `φ = w / √(w ⬝ w)` of the block problem. -/
theorem local_solution {a ν δ : ℝ} {Ψ H : Fin N → ℂ} (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1024) (hΨ : cNorm Ψ ≤ 5 / 4)
    (hΨΨ : ‖Ψ ⬝ᵥ Ψ - 1‖ ≤ 2 * δ) (hH : ν * cNorm (H - Ψ) ≤ 6 * δ) :
    (1 / 8 : ℝ) ≤ (cBlend a ν Ψ H ⬝ᵥ cBlend a ν Ψ H).re ∧
      cMinimizer a ν Ψ H ⬝ᵥ cMinimizer a ν Ψ H = 1 ∧
      cNorm (cMinimizer a ν Ψ H - Ψ) ≤ 500 * δ ∧ ‖cMultiplier a ν Ψ H‖ ≤ 128 * δ := by
  set s0 : ℝ := a + ν with hs0
  have hs0l : 1 / 2 ≤ s0 := by linarith
  have hs0u : s0 ≤ 3 := by linarith
  set e : Fin N → ℂ := (ν : ℂ) • (H - Ψ) with he
  have hen : cNorm e ≤ 6 * δ := by
    rw [he, cNorm_smul]
    simpa [abs_of_nonneg hν0] using hH
  have hw : cBlend a ν Ψ H = (s0 : ℂ) • Ψ + e := by
    funext i
    simp only [cBlend, he, hs0, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    push_cast; ring
  clear_value e
  set w := cBlend a ν Ψ H with hwdef
  clear_value w
  have hdot : w ⬝ᵥ w = (s0 : ℂ) ^ 2 * (Ψ ⬝ᵥ Ψ) + 2 * (s0 : ℂ) * (Ψ ⬝ᵥ e) + e ⬝ᵥ e := by
    rw [hw, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct, smul_dotProduct,
      dotProduct_smul, dotProduct_smul, dotProduct_comm e Ψ]
    simp only [smul_eq_mul]
    ring
  have hζ : ‖w ⬝ᵥ w - (s0 : ℂ) ^ 2‖ ≤ 64 * δ := by
    have : w ⬝ᵥ w - (s0 : ℂ) ^ 2 =
        (s0 : ℂ) ^ 2 * (Ψ ⬝ᵥ Ψ - 1) + 2 * (s0 : ℂ) * (Ψ ⬝ᵥ e) + e ⬝ᵥ e := by
      rw [hdot]; ring
    rw [this]
    have h1 : ‖(s0 : ℂ) ^ 2 * (Ψ ⬝ᵥ Ψ - 1)‖ ≤ 9 * (2 * δ) := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      have : s0 ^ 2 ≤ 9 := by nlinarith
      exact mul_le_mul this hΨΨ (norm_nonneg _) (by norm_num)
    have h2 : ‖2 * (s0 : ℂ) * (Ψ ⬝ᵥ e)‖ ≤ 6 * (5 / 4 * (6 * δ)) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      have h3 : ‖Ψ ⬝ᵥ e‖ ≤ 5 / 4 * (6 * δ) :=
        (norm_dotProduct_le _ _).trans (mul_le_mul hΨ hen (cNorm_nonneg _) (by norm_num))
      have : ‖(2 : ℂ)‖ * s0 ≤ 6 := by simp; linarith
      exact mul_le_mul this h3 (norm_nonneg _) (by norm_num)
    have h3 : ‖e ⬝ᵥ e‖ ≤ (6 * δ) * (6 * δ) :=
      (norm_dotProduct_le _ _).trans (mul_le_mul hen hen (cNorm_nonneg _) (by linarith))
    calc _ ≤ ‖(s0 : ℂ) ^ 2 * (Ψ ⬝ᵥ Ψ - 1) + 2 * (s0 : ℂ) * (Ψ ⬝ᵥ e)‖ + ‖e ⬝ᵥ e‖ := norm_add_le _ _
      _ ≤ ‖(s0 : ℂ) ^ 2 * (Ψ ⬝ᵥ Ψ - 1)‖ + ‖2 * (s0 : ℂ) * (Ψ ⬝ᵥ e)‖ + ‖e ⬝ᵥ e‖ := by
          linarith [norm_add_le ((s0 : ℂ) ^ 2 * (Ψ ⬝ᵥ Ψ - 1)) (2 * (s0 : ℂ) * (Ψ ⬝ᵥ e))]
      _ ≤ 9 * (2 * δ) + 6 * (5 / 4 * (6 * δ)) + (6 * δ) * (6 * δ) := by linarith
      _ ≤ 64 * δ := by nlinarith
  have hre : (1 / 8 : ℝ) ≤ (w ⬝ᵥ w).re := by
    have h1 : |(w ⬝ᵥ w - (s0 : ℂ) ^ 2).re| ≤ 64 * δ :=
      (Complex.abs_re_le_norm _).trans hζ
    have h2 : ((w ⬝ᵥ w - (s0 : ℂ) ^ 2).re) = (w ⬝ᵥ w).re - s0 ^ 2 := by
      simp [sq]
    rw [h2] at h1
    have := (abs_le.1 h1).1
    nlinarith
  have hne : w ⬝ᵥ w ≠ 0 := by
    intro h0; rw [h0] at hre; simp at hre; linarith
  set s := sqrtDot w with hsdef
  have hs2 : s ^ 2 = w ⬝ᵥ w := sqrtDot_sq w
  have hsre : 0 ≤ s.re := re_sqrtDot_nonneg w
  have hsn : 1 / 3 ≤ ‖s‖ := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : ‖s‖ ^ 2 = ‖w ⬝ᵥ w‖ := by rw [← hs2, norm_pow]
    have h2 : (w ⬝ᵥ w).re ≤ ‖w ⬝ᵥ w‖ := (Complex.re_le_norm _)
    have h3 : ‖s‖ ^ 2 < 1 / 9 := by
      have := norm_nonneg s
      nlinarith
    linarith
  have hsne : s ≠ 0 := by
    intro h0; rw [h0] at hsn; simp at hsn; linarith
  have hsd : ‖s - (s0 : ℂ)‖ ≤ 128 * δ := by
    have hprod : (s - (s0 : ℂ)) * (s + (s0 : ℂ)) = w ⬝ᵥ w - (s0 : ℂ) ^ 2 := by
      rw [← hs2]; ring
    have hlow : 1 / 2 ≤ ‖s + (s0 : ℂ)‖ := by
      refine le_trans ?_ (Complex.abs_re_le_norm _)
      have : (s + (s0 : ℂ)).re = s.re + s0 := by simp
      rw [this, abs_of_nonneg (by linarith)]
      linarith
    have : ‖s - (s0 : ℂ)‖ * (1 / 2) ≤ 64 * δ := by
      calc ‖s - (s0 : ℂ)‖ * (1 / 2) ≤ ‖s - (s0 : ℂ)‖ * ‖s + (s0 : ℂ)‖ :=
            mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
        _ = ‖w ⬝ᵥ w - (s0 : ℂ) ^ 2‖ := by rw [← norm_mul, hprod]
        _ ≤ 64 * δ := hζ
    linarith
  refine ⟨hre, cMinimizer_dot (by rw [← hwdef]; exact hne), ?_, ?_⟩
  · have hφ : cMinimizer a ν Ψ H - Ψ = s⁻¹ • (e + ((s0 : ℂ) - s) • Ψ) := by
      funext i
      have h1 : w i = (s0 : ℂ) * Ψ i + e i := by
        have := congrFun hw i
        simpa using this
      simp only [cMinimizer, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      rw [← hwdef, ← hsdef, h1]
      field_simp
      ring
    rw [hφ, cNorm_smul, norm_inv]
    have h1 : cNorm (e + ((s0 : ℂ) - s) • Ψ) ≤ 6 * δ + 128 * δ * (5 / 4) := by
      refine (cNorm_add_le _ _).trans (add_le_add hen ?_)
      rw [cNorm_smul, norm_sub_rev]
      exact mul_le_mul hsd hΨ (cNorm_nonneg _) (by linarith)
    have h2 : ‖s‖⁻¹ ≤ 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc ‖s‖⁻¹ * cNorm (e + ((s0 : ℂ) - s) • Ψ) ≤ 3 * (6 * δ + 128 * δ * (5 / 4)) :=
          mul_le_mul h2 h1 (cNorm_nonneg _) (by norm_num)
      _ ≤ 500 * δ := by nlinarith
  · have : cMultiplier a ν Ψ H = s - (s0 : ℂ) := by
      simp only [cMultiplier]; rw [← hwdef, ← hsdef]; simp only [hs0]; push_cast; ring
    rw [this]; exact hsd


/-! ### From the data conditions to the three hypotheses -/

theorem cNorm_cplx_eq_rn (x : Fin N → ℝ) : cNorm (cplx x) = rn x := by
  have h : cNorm (cplx x) ^ 2 = ∑ i, x i ^ 2 := by
    rw [cNorm_cplx_sq]; simp [dotProduct, sq]
  unfold rn
  rw [← h, Real.sqrt_sq (cNorm_nonneg _)]

/-- The unit vector `q = ψ / |ψ|` as a complex vector. -/
noncomputable def qvec (ψ : Fin N → ℝ) : Fin N → ℂ := ((rn ψ : ℝ) : ℂ)⁻¹ • cplx ψ

theorem rn_sq (x : Fin N → ℝ) : rn x ^ 2 = ∑ i, x i ^ 2 := by
  unfold rn; rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

/-- Facts on `q = ψ / |ψ|` from (R2), (R3), (R4). -/
theorem q_facts {ψ h : Fin N → ℝ} {δ B : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 16) (hB0 : 0 ≤ B)
    (hB1 : B ≤ 1) (hψ : |∑ i, ψ i ^ 2 - 1| < δ)
    (hr3 : B * |1 - (∑ i, ψ i * h i) / rn ψ| < δ ^ 2) (hr4 : B * |∑ i, h i ^ 2 - 1| < δ ^ 2) :
    cNorm (cplx ψ - qvec ψ) ≤ δ ∧ B * cNorm (cplx h - qvec ψ) ≤ 2 * δ ∧
      B * cNorm (cplx h - qvec ψ) ^ 2 ≤ 3 * δ ^ 2 := by
  have hs := abs_lt.1 hψ
  have hρ2 := rn_sq ψ
  have hρ0 : 0 ≤ rn ψ := Real.sqrt_nonneg _
  have hρpos : 0 < rn ψ := by
    rcases hρ0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hρ2; nlinarith
  have hρ1 : |rn ψ - 1| < δ := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hq : cNorm (cplx ψ - qvec ψ) = |rn ψ - 1| := by
    have : cplx ψ - qvec ψ = (1 - ((rn ψ : ℝ) : ℂ)⁻¹) • cplx ψ := by
      unfold qvec; rw [sub_smul, one_smul]
    rw [this, cNorm_smul, cNorm_cplx_eq_rn]
    have : ‖(1 - ((rn ψ : ℝ) : ℂ)⁻¹)‖ * rn ψ = |rn ψ - 1| := by
      have e : (1 - ((rn ψ : ℝ) : ℂ)⁻¹) = (((1 - (rn ψ)⁻¹ : ℝ)) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs, ← abs_of_pos hρpos, ← abs_mul,
        abs_of_pos hρpos]
      congr 1
      field_simp
    exact this
  have hdist : cNorm (cplx h - qvec ψ) ^ 2 = ∑ i, h i ^ 2 - 2 * ((∑ i, ψ i * h i) / rn ψ) + 1 := by
    rw [cNorm_sq]
    have : ∀ i, ‖(cplx h - qvec ψ) i‖ ^ 2 =
        h i ^ 2 - 2 * (ψ i * h i) / rn ψ + ψ i ^ 2 / rn ψ ^ 2 := by
      intro i
      have e : (cplx h - qvec ψ) i = (((h i - (rn ψ)⁻¹ * ψ i : ℝ)) : ℂ) := by
        simp [cplx, qvec]
      rw [e, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      field_simp
      ring
    rw [Finset.sum_congr rfl fun i _ => this i]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
      ← Finset.mul_sum, mul_div_assoc, ← hρ2]
    field_simp
  have hmain : B * cNorm (cplx h - qvec ψ) ^ 2 ≤ 3 * δ ^ 2 := by
    rw [hdist]
    have a1 : B * (∑ i, h i ^ 2 - 1) ≤ B * |∑ i, h i ^ 2 - 1| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hB0
    have a2 : B * (1 - (∑ i, ψ i * h i) / rn ψ) ≤ B * |1 - (∑ i, ψ i * h i) / rn ψ| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hB0
    nlinarith
  refine ⟨hq.le.trans hρ1.le, ?_, hmain⟩
  have hX : 0 ≤ cNorm (cplx h - qvec ψ) := cNorm_nonneg _
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [mul_nonneg hB0 hX]


section Site

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)

theorem cplx_add_eq (ψ : Fin N → ℝ) (ψ' : Fin N → ℂ) :
    (fun i => (ψ i : ℂ) + ψ' i) = cplx ψ + ψ' := rfl

/-- (R2), (C2): the hypotheses on `Ψ` of `local_solution`. -/
theorem site_Ψ_hyp {ν δ ε : ℝ} {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h : Fin N → ℝ}
    {Ψ' h' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hP : InPsiTildeC G ν δ ε Ψ h Ψ' h')
    (hδε : δ ≤ ε) (hε : ε ≤ 1 / 16) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G)
    (Ψt : Fin N → ℂ) (hΨt : ∀ i, Ψt i = Ψ x i + Ψ' x i) :
    cNorm Ψt ≤ 5 / 4 ∧ ‖Ψt ⬝ᵥ Ψt - 1‖ ≤ 2 * δ := by
  have hr2 := hP.r2 x hx
  have hδ0 : 0 < δ := lt_of_le_of_lt (abs_nonneg _) hr2
  have hΨe : Ψt = cplx (Ψ x) + Ψ' x := funext fun i => by simp [hΨt, cplx]
  constructor
  · rw [hΨe]
    refine (cNorm_add_le _ _).trans ?_
    have h1 : cNorm (cplx (Ψ x)) ≤ 9 / 8 := by
      rw [cNorm_cplx_eq_rn]
      have h2 := rn_sq (Ψ x)
      have h3 := (abs_lt.1 hr2).2
      have h4 : 0 ≤ rn (Ψ x) := Real.sqrt_nonneg _
      nlinarith
    have h5 : cNorm (Ψ' x) ≤ ε + δ := (hP.c2a x hx).le
    linarith
  · have h1 := hP.c2b x hx
    have h2 : Ψt ⬝ᵥ Ψt = ∑ i, ((Ψ x i : ℂ) + Ψ' x i) * ((Ψ x i : ℂ) + Ψ' x i) := by
      unfold dotProduct; simp [hΨt]
    have h3 : ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ) - 1 = (((∑ i, Ψ x i ^ 2 - 1 : ℝ)) : ℂ) := by
      push_cast; simp [sq]
    have h4 : ‖Ψt ⬝ᵥ Ψt - 1‖ ≤ ‖Ψt ⬝ᵥ Ψt - ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ)‖ +
        ‖∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ) - 1‖ := by
      have := norm_add_le (Ψt ⬝ᵥ Ψt - ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ))
        (∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ) - 1)
      simpa using this
    rw [h2] at h4 ⊢
    rw [h3, Complex.norm_real, Real.norm_eq_abs] at h4
    linarith

/-- (R2)-(R4), (C3): the mass hypothesis of `local_solution` at a site of `Ω₁`. -/
theorem site_H_hyp {ν δ ε : ℝ} {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ' h' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hP : InPsiTildeC G ν δ ε Ψ h₀ Ψ' h')
    (hδε : δ ≤ ε) (hε : ε ≤ 1 / 16) (hν0 : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hL : 1 ≤ L) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ G.Ω 1) (Ψt Ht : Fin N → ℂ) (hΨt : ∀ i, Ψt i = Ψ y i + Ψ' y i)
    (hHt : ∀ i, Ht i = h₀ i + h' y i) :
    ν * ((L : ℝ) ^ G.layerIndex y) ^ 2 * cNorm (Ht - Ψt) ≤ 6 * δ := by
  have hyd : y ∈ dataSites G := (mem_dataSites G).2 (Or.inl hy)
  have hr2 := hP.r2 y hyd
  have hδ0 : 0 < δ := lt_of_le_of_lt (abs_nonneg _) hr2
  obtain ⟨hm1, hmk, _⟩ := G.layerIndex_spec hy
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set B : ℝ := ν * ((L : ℝ) ^ G.layerIndex y) ^ 2 with hB
  have hLm : ((L : ℝ) ^ G.layerIndex y) ^ 2 ≤ ((L : ℝ) ^ k) ^ 2 := by
    have := pow_le_pow_right₀ hL' hmk
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ L) (G.layerIndex y)]
  have hBk : B ≤ ν * ((L : ℝ) ^ k) ^ 2 := mul_le_mul_of_nonneg_left hLm hν0
  have hB0 : 0 ≤ B := by positivity
  have hB1 : B ≤ 1 := hBk.trans hν1
  have hr3 := hP.r3 y hyd
  have hr4 : B * |∑ i, h₀ i ^ 2 - 1| < δ ^ 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hBk (abs_nonneg _)) (hP.r4)
  obtain ⟨hq1, hq2, -⟩ := q_facts hδ0.le (by linarith) hB0 hB1 hr2 hr3 hr4
  have hHΨ : Ht - Ψt = (cplx h₀ - qvec (Ψ y)) + (qvec (Ψ y) - cplx (Ψ y)) + (h' y - Ψ' y) := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, hΨt, hHt, cplx]
    ring
  have hc3 : B * cNorm (h' y) ≤ δ := by
    have := (hP.c3a y hy).le
    have h2 : δ ^ 2 / ε ≤ δ := by
      rw [div_le_iff₀ hP.eps_pos]; nlinarith
    exact this.trans h2
  have hBε : B * ε ≤ δ := by
    have h1 : B * ε ^ 2 ≤ δ ^ 2 := le_trans (mul_le_mul_of_nonneg_right hBk (sq_nonneg _)) hνε
    have h2 : (B * ε) ^ 2 ≤ δ ^ 2 := by nlinarith [sq_nonneg ε]
    have := hP.eps_pos
    by_contra hlt
    rw [not_le] at hlt
    nlinarith
  have hψ' : B * cNorm (Ψ' y) ≤ 2 * δ := by
    have h1 : cNorm (Ψ' y) ≤ ε + δ := (hP.c2a y hyd).le
    calc B * cNorm (Ψ' y) ≤ B * (ε + δ) := mul_le_mul_of_nonneg_left h1 hB0
      _ = B * ε + B * δ := by ring
      _ ≤ 2 * δ := by nlinarith
  rw [hHΨ]
  have hq1' : cNorm (qvec (Ψ y) - cplx (Ψ y)) ≤ δ := by
    rw [← neg_sub]
    have : cNorm (-(cplx (Ψ y) - qvec (Ψ y))) = cNorm (cplx (Ψ y) - qvec (Ψ y)) := by
      have := cNorm_smul (-1 : ℂ) (cplx (Ψ y) - qvec (Ψ y))
      simpa using this
    rw [this]; exact hq1
  calc B * cNorm ((cplx h₀ - qvec (Ψ y)) + (qvec (Ψ y) - cplx (Ψ y)) + (h' y - Ψ' y))
      ≤ B * (cNorm (cplx h₀ - qvec (Ψ y)) + cNorm (qvec (Ψ y) - cplx (Ψ y)) +
          (cNorm (h' y) + cNorm (Ψ' y))) := by
        refine mul_le_mul_of_nonneg_left ?_ hB0
        refine (cNorm_add_le _ _).trans (add_le_add ((cNorm_add_le _ _)) (cNorm_sub_le _ _))
    _ = B * cNorm (cplx h₀ - qvec (Ψ y)) + B * cNorm (qvec (Ψ y) - cplx (Ψ y)) +
          B * cNorm (h' y) + B * cNorm (Ψ' y) := by ring
    _ ≤ 2 * δ + δ + δ + 2 * δ := by
        have : B * cNorm (qvec (Ψ y) - cplx (Ψ y)) ≤ δ :=
          (mul_le_mul hB1 hq1' (cNorm_nonneg _) zero_le_one).trans (by linarith)
        linarith
    _ = 6 * δ := by ring

end Site

end Balaban.Background
