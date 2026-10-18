/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectFiled

/-!
# The filed torus defect at the origin, power form

The exponential decay in the covering threshold of the torus is a power of the side: for
`p > 0`, `c > 0` the maximum of `y^p e^{-c y}` is `(p/(e c))^p`. The constant `C_R` is
explicit and does not depend on `N₁`, `k`, `j` or the datum.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

/-- The maximum of `y^p e^{-c y}` over `y > 0`. -/
theorem rpow_mul_exp_neg_le {p c y : ℝ} (hp : 0 < p) (hc : 0 < c) (hy : 0 < y) :
    y ^ p * Real.exp (-(c * y)) ≤ (p / (Real.exp 1 * c)) ^ p := by
  have hz : 0 < c * y := mul_pos hc hy
  have h1 : Real.log (c * y / p) ≤ c * y / p - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : p * Real.log (c * y) - c * y ≤ p * Real.log p - p := by
    have h3 : Real.log (c * y / p) = Real.log (c * y) - Real.log p :=
      Real.log_div hz.ne' hp.ne'
    rw [h3] at h1
    have := mul_le_mul_of_nonneg_left h1 hp.le
    have h4 : p * (c * y / p - 1) = c * y - p := by field_simp
    nlinarith
  have h5 : (c * y) ^ p * Real.exp (-(c * y)) ≤ p ^ p * Real.exp (-p) := by
    rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos hp, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  have h6 : y ^ p = (c * y) ^ p / c ^ p := by
    rw [Real.mul_rpow hc.le hy.le]
    have : (0 : ℝ) < c ^ p := Real.rpow_pos_of_pos hc p
    field_simp
  have h7 : (p / (Real.exp 1 * c)) ^ p = p ^ p * Real.exp (-p) / c ^ p := by
    rw [Real.div_rpow hp.le (by positivity), Real.mul_rpow (Real.exp_pos 1).le hc.le,
      Real.exp_one_rpow]
    have : (0 : ℝ) < c ^ p := Real.rpow_pos_of_pos hc p
    rw [Real.exp_neg]
    field_simp
  rw [h6, h7, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right h5 (Real.rpow_pos_of_pos hc p).le


/-- The covering threshold gives a power of the side as the decay of the filed defect. -/
theorem exp_neg_half_threshold_le {A Q B c' y p : ℝ} (hA : 0 < A) (hc' : 0 < c') (hy : 0 < y)
    (hp : 0 < p) (hB : c' * y ≤ B) :
    Real.exp (-(((B - 4 * Q - 4) / (4 * A) - 1) / 2)) ≤
      Real.exp ((4 * Q + 4) / (8 * A) + 1 / 2) * (p / (Real.exp 1 * (c' / (8 * A)))) ^ p *
        y ^ (-p) := by
  have hc : 0 < c' / (8 * A) := by positivity
  have h1 : -(((B - 4 * Q - 4) / (4 * A) - 1) / 2) ≤
      (4 * Q + 4) / (8 * A) + 1 / 2 - (c' / (8 * A)) * y := by
    have : (c' * y) / (8 * A) ≤ B / (8 * A) := div_le_div_of_nonneg_right hB (by positivity)
    have e : -(((B - 4 * Q - 4) / (4 * A) - 1) / 2) =
        (4 * Q + 4) / (8 * A) + 1 / 2 - B / (8 * A) := by field_simp; ring
    rw [e]
    have : (c' / (8 * A)) * y = (c' * y) / (8 * A) := by ring
    linarith
  have h2 := rpow_mul_exp_neg_le hp hc hy
  have hyp : 0 < y ^ p := Real.rpow_pos_of_pos hy p
  have h3 : Real.exp (-((c' / (8 * A)) * y)) ≤ (p / (Real.exp 1 * (c' / (8 * A)))) ^ p * y ^ (-p) := by
    rw [Real.rpow_neg hy.le]
    rw [le_mul_inv_iff₀ hyp]
    linarith
  calc Real.exp (-(((B - 4 * Q - 4) / (4 * A) - 1) / 2))
      ≤ Real.exp ((4 * Q + 4) / (8 * A) + 1 / 2 - (c' / (8 * A)) * y) := Real.exp_le_exp.2 h1
    _ = Real.exp ((4 * Q + 4) / (8 * A) + 1 / 2) * Real.exp (-((c' / (8 * A)) * y)) := by
        rw [← Real.exp_add]; congr 1
    _ ≤ Real.exp ((4 * Q + 4) / (8 * A) + 1 / 2) *
        ((p / (Real.exp 1 * (c' / (8 * A)))) ^ p * y ^ (-p)) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = _ := by ring

end Balaban.SmallField.Def6

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ}
  {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

open Classical in
/-- **The filed torus defect at the origin, power form** (P1 pp. 118–119 (H.6)–(H.7), pp. 152–153
Prop. 3.10, (3.126)–(3.128)): `|R_j^T(0)| ≤ C_R E₀ L^{-(d+α₃)(k-j)}`, `α₃ = 1 - 2γ - α₁`, with `C_R`
independent of the torus (`N₁`), of `k`, of `j` and of the datum. The datum enters through
`DataHypAniso` in the conclusion shape of `xiC_dataHypAniso_of_levelGS` (any domain containing the
two points), with the second difference bound and the numerical conditions of the termwise bound. -/
theorem norm_filed_origin_le_power
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P.m₀ ∣ N₁)
    (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ)
    {σ ε K₂ Λ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (hεΛ : ε ≤ Λ * anisoRadius d L N P j) (hτ : σ ^ 2 * ε ≤ 1 / 4)
    (hdat : ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
      ((fun s => Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)),
          ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) ∈ Dom ∧
        ((fun _ => Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j 0)),
          ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) ∈ Dom →
      (∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) →
      DataHypAniso Dom (nuIdeal L k (Rg.ν k) j) σ ε K₂
        (fun s => Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        (((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv))
    (hsec : ∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) :
    ‖∑ᶠ Z ∈ polysAt P.m₀ j (0 : CTorus d L N₁ m₁ k),
        (let e : Fld d L N₁ m₁ k N := constFld (Pi.single i₀ 1)
       let blk : Set (CTorus d L N₁ m₁ k) → Finset (CTorus d L N₁ m₁ k) := fun Z' =>
         Finset.univ.filter fun x => Aligned (L ^ j) x ∧ x ∈ Z'
       let u : ℂ := sqrtC (dot (Ψ 0) (Ψ 0))
       let dΨ : Fin d → Fin N → ℂ := fun μ =>
         Ψ (0 + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ 0
       let g : Fin d → Fin d → ℂ := fun μ μ' =>
         dot (dΨ μ) (dΨ μ') - dot (Ψ 0) (dΨ μ) * dot (Ψ 0) (dΨ μ') /
           dot (Ψ 0) (Ψ 0)
       let lift : CTorus d L N₁ m₁ k → Fin d → ℂ := fun z μ =>
         ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - 0) μ : ℤ) : ℂ)
       let a : Set (CTorus d L N₁ m₁ k) → CTorus d L N₁ m₁ k → ℂ := fun Z' x =>
         fderiv ℂ (fun Ψ' => (Tm N₁).E j 0 Z' Ψ' e) e (blockDir L j x i₀)
       (Tm N₁).E j 0 Z e e + (u - 1) * ∑ x ∈ blk Z, a Z x
             + (dot (Ψ 0) ((constFld hv : Fld d L N₁ m₁ k N) 0) / u - 1) *
               fderiv ℂ (fun h' => (Tm N₁).E j 0 Z e h') e e
             - (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' * ∑ x ∈ blk Z, ∑ x' ∈ blk Z,
                 D2 (fun Ψ' => (Tm N₁).E j 0 Z Ψ' e) e (blockDir L j x i₁)
                   (blockDir L j x' i₁) *
                   ((lift x μ - lift x' μ) * (lift x μ' - lift x' μ')))‖ ≤
      (2 * (24 * Real.exp 1 * (16 * (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 + (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 * (N * (N * 40 * Λ) ^ 2))) * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)) * (Real.exp ((4 * (((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ)) + 4) / (8 * (diamA d L P.m₀ m₁)) + 1 / 2) * ((((d : ℝ) + (1 - 2 * P.γ - P.α₁))) / (Real.exp 1 * (((L : ℝ) ^ (P.m₀ + m₁)) / (8 * (diamA d L P.m₀ m₁))))) ^ (((d : ℝ) + (1 - 2 * P.γ - P.α₁)))))) * P.E₀ *
        (((L : ℝ) ^ (k - j)) ^ (-(((d : ℝ) + (1 - 2 * P.γ - P.α₁))))) := by
  have h := norm_filed_origin_le hF hn hne hN Ψ hv hσ hσ1 hε hεΛ hτ hdat hsec
  refine h.trans ?_
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hn.hd
  have hA : 0 < (diamA d L P.m₀ m₁) := diamA_pos hd (NeZero.pos L) P.m₀ m₁
  have hL0 : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  have hp : 0 < (((d : ℝ) + (1 - 2 * P.γ - P.α₁))) := by
    have := hF.admissible.α₁_lt
    have : (0 : ℝ) < d := by exact_mod_cast hd
    linarith
  have hy : 0 < ((L : ℝ) ^ (k - j)) := by positivity
  have hc' : 0 < ((L : ℝ) ^ (P.m₀ + m₁)) := by positivity
  have hN1 : L ^ P.m₀ ≤ N₁ := Nat.le_of_dvd (NeZero.pos N₁) hN
  have hB : ((L : ℝ) ^ (P.m₀ + m₁)) * ((L : ℝ) ^ (k - j)) ≤
      (((N₁ * L ^ m₁ * L ^ (k - j) : ℕ)) : ℝ) := by
    have h1 : ((L : ℝ) ^ P.m₀) ≤ (N₁ : ℝ) := by exact_mod_cast hN1
    push_cast
    have h2 : (0 : ℝ) ≤ (L : ℝ) ^ m₁ * (L : ℝ) ^ (k - j) := by positivity
    calc ((L : ℝ) ^ (P.m₀ + m₁)) * ((L : ℝ) ^ (k - j))
        = (L : ℝ) ^ P.m₀ * ((L : ℝ) ^ m₁ * (L : ℝ) ^ (k - j)) := by rw [pow_add]; ring
      _ ≤ (N₁ : ℝ) * ((L : ℝ) ^ m₁ * (L : ℝ) ^ (k - j)) := mul_le_mul_of_nonneg_right h1 h2
      _ = _ := by ring
  have hexp := exp_neg_half_threshold_le (Q := (((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ))) hA hc' hy hp hB
  have hCst0 : 0 ≤ (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 + (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 * (N * (N * 40 * Λ) ^ 2)) := by
    have hΛ : 0 ≤ Λ := by
      have := (hF.anisoRadiusOK hn.hsmall i₀).1
      by_contra h
      push Not at h
      nlinarith
    have hH : 0 ≤ c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d := by
      have : 0 ≤ c1 d L := by unfold c1; positivity
      positivity
    positivity
  have hK0 : 0 ≤ ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)) := by
    have : 0 ≤ K0 d L (P.κ - 2) := (K0_pos d L (P.κ - 2)).le
    positivity
  have hE0 := hF.admissible.E₀_nonneg
  calc _ ≤ 2 * (24 * Real.exp 1 * (16 * (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 + (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 * (N * (N * 40 * Λ) ^ 2))) * P.E₀ *
        (Real.exp ((4 * (((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ)) + 4) / (8 * (diamA d L P.m₀ m₁)) + 1 / 2) *
          ((((d : ℝ) + (1 - 2 * P.γ - P.α₁))) / (Real.exp 1 * (((L : ℝ) ^ (P.m₀ + m₁)) / (8 * (diamA d L P.m₀ m₁))))) ^ (((d : ℝ) + (1 - 2 * P.γ - P.α₁))) *
          (((L : ℝ) ^ (k - j)) ^ (-(((d : ℝ) + (1 - 2 * P.γ - P.α₁)))))) * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2))) := by
        gcongr
    _ = _ := by ring

end Balaban.SmallField.Def6v2
