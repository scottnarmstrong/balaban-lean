/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTaggedWeightedGfin
public import Balaban.Green.FinalTorusCloseUnif
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Distance-weighted closeness of the perturbed defect and of the last-integral coefficients

Continuation of `Green/FinalTaggedWeightedGfin` (blocker 7).  The perturbed defect
`K_E = R_z - E χ_z G_z` of the final operators on two tori, with `E`, `E'` small perturbations that
decay at the rate `rE ≥ pdEps / 4`, is close up to `δ e^{-(pdEps/8) dist(x, y)}` with `δ` of order
`√ε + √εE` (`final_boxE_close_weighted`), and the tagged defect up to `|C| e^{H κ} δ`, with no
factor `e^{κ |C|}` (`final_taggedKE_close_weighted`).  Through the shared cores
`final_coef_logdet_close_core` and `final_coef_cutoffInteraction_close_core` of
`FinalTaggedTorusClose` this gives the coefficients of the logarithm of the determinant and of the
cutoff interaction with constants independent of the number of cells `nC ≥ |C|`, and a polynomial
factor in `nC` (`final_coef_logdet_close_twoTorus_unif_weighted`,
`final_coef_cutoffInteraction_close_twoTorus_unif_weighted`).
-/

@[expose] public section

open Finset Matrix Balaban.Localization MeasureTheory

namespace Balaban.Green

/-- `‖a X - a' X'‖ ≤ ‖a - a'‖ ‖X‖ + ‖a'‖ ‖X - X'‖`. -/
theorem norm_mul_sub_mul_le' (a a' X X' : ℂ) :
    ‖a * X - a' * X'‖ ≤ ‖a - a'‖ * ‖X‖ + ‖a'‖ * ‖X - X'‖ := by
  have : a * X - a' * X' = (a - a') * X + a' * (X - X') := by ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]

/-- Combination of two weighted bounds for a product. -/
theorem prod_close_pointwise {a a' X X' : ℂ} {α η B δ ex ey ez : ℝ} (hα : 0 ≤ α) (hη : 0 ≤ η)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hex : 0 ≤ ex)
    (ha : ‖a - a'‖ ≤ α * ex) (ha' : ‖a'‖ ≤ η * ex) (hX : ‖X‖ ≤ B * ey)
    (hXd : ‖X - X'‖ ≤ δ * ey) (hz : ex * ey ≤ ez) :
    ‖a * X - a' * X'‖ ≤ (B * α + η * δ) * ez := by
  refine (norm_mul_sub_mul_le' a a' X X').trans ?_
  calc _ ≤ (α * ex) * (B * ey) + (η * ex) * (δ * ey) :=
        add_le_add (mul_le_mul ha hX (norm_nonneg _) (by positivity))
          (mul_le_mul ha' hXd (norm_nonneg _) (by positivity))
    _ = (B * α + η * δ) * (ex * ey) := by ring
    _ ≤ (B * α + η * δ) * ez := mul_le_mul_of_nonneg_left hz (by positivity)

theorem exp_neg_mul_anti' {σ r t : ℝ} (ht : 0 ≤ t) (h : σ ≤ r) :
    Real.exp (-r * t) ≤ Real.exp (-σ * t) :=
  Real.exp_le_exp.2 (by nlinarith)

theorem exp_mul_exp_le' {σ a b c : ℝ} (hσ : 0 ≤ σ) (h : c ≤ a + b) :
    Real.exp (-σ * a) * Real.exp (-σ * b) ≤ Real.exp (-σ * c) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 (by nlinarith)

section TwoTorus

variable {d k M J N N' L : ℕ} [NeZero N] [NeZero N'] [NeZero L]

/-- **Distance-weighted closeness of `E χ_z G_z`** for the final operators on two tori.  With
`E`, `E'` `(rE, η)`-small, `rE ≥ pdEps / 4`, close up to `εE` on `Y(C)²`, and the final operators
close up to `ε`, the entries of `E χ_z G_z` differ at `x, y ∈ Y(C)` by at most
`nB (2 T √(2 η εE) + η δG) e^{-(pdEps/8) dist(x, y)}`, `T = (g + t)⁻¹`, `nB = (8M+1)^d`,
`δG = √(nB² ε T² · 4T)`. -/
theorem final_boxE_close_weighted (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) {ε εE η rE : ℝ}
    (hrE : pdEps d L / 4 ≤ rE) (hη : 0 ≤ η)
    (hU : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤ ε)
    {E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {E' : Matrix (L1Torus d N') (L1Torus d N') ℂ}
    (hE : WSmall rE η E) (hE' : WSmall rE η E')
    (hEc : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, ‖E x y - E' (f x) (f y)‖ ≤ εE)
    {t : ℝ} (ht : 0 ≤ t) {z : MacIdx d N M} (hzC : z ∈ C) {x y : L1Torus d N}
    (hx : x ∈ macRegion d N M C) (hy : y ∈ macRegion d N M C) :
    ‖(E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N k v a) (macBoxF d N M z) t)) x y -
        (E' * (Matrix.diagonal (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) *
          boxG (finalOp d L N' k v a) (macBoxF d N' M (e z)) t)) (f x) (f y)‖ ≤
      (((8 * M + 1) ^ d : ℕ) : ℝ) *
        ((2 * (finalGap d L + t)⁻¹ * Real.sqrt (εE * (2 * η)) +
            η * Real.sqrt ((((((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2) *
              (4 * (finalGap d L + t)⁻¹)))) *
          Real.exp (-(pdEps d L / 8) * dist x y)) := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hgt : 0 < finalGap d L + t := by linarith
  have hT0 : 0 < (finalGap d L + t)⁻¹ := inv_pos.2 hgt
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hU x hx y hy)
  have hεE0 : 0 ≤ εE := (norm_nonneg _).trans (hEc x hx y hy)
  have hεp := pdEps_pos (d := d) (L := L) hd
  set Yset : Finset (L1Torus d N) := Finset.univ.filter (fun u => u ∈ macRegion d N M C) with hYset
  have hYmem : ∀ u, u ∈ Yset ↔ u ∈ macRegion d N M C := fun u => by simp [hYset]
  obtain ⟨hBY, hinjY, hc, hc', hcY⟩ := boxFamily_twoTorus hM hN hN' hf he hC hYmem hzC
  have hBimg := macBoxF_image hM hN hN' hf (fun y μ => rfl) he (hC z hzC)
    (g := fun y μ => (((y μ).val : ℕ) : ZMod N))
  have hBcard : ((macBoxF d N M z).card : ℝ) ≤ (((8 * M + 1) ^ d : ℕ) : ℝ) := by
    exact_mod_cast card_macBoxF_le hM z
  set nB : ℝ := (((8 * M + 1) ^ d : ℕ) : ℝ) with hnBdef
  have hnB : 0 ≤ nB := by positivity
  have hBinj : Set.InjOn f (macBoxF d N M z : Set (L1Torus d N)) :=
    hinjY.mono (by exact_mod_cast hBY)
  rw [hBimg]
  set T : ℝ := (finalGap d L + t)⁻¹ with hT
  set σ : ℝ := pdEps d L / 8 with hσ
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  have hrE0 : 0 < rE := lt_of_lt_of_le (by positivity) hrE
  have hσr : σ ≤ rE / 2 := by rw [hσ]; linarith
  have hσfr : σ ≤ finalRate d L := by
    have : pdEps d L ≤ finalRate d L := min_le_right _ _
    rw [hσ]; linarith
  set α : ℝ := Real.sqrt (εE * (2 * η)) with hα
  set δG : ℝ := Real.sqrt (((nB ^ 2 * ε * T ^ 2) * (4 * T))) with hδG
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  have hδG0 : 0 ≤ δG := Real.sqrt_nonneg _
  have hsum0 : 0 ≤ 2 * T * α + η * δG := by positivity
  have hK0 : 0 ≤ (2 * T * α + η * δG) * Real.exp (-σ * dist x y) := by positivity
  have hc1 : ∀ (N₀ : ℕ) [NeZero N₀] (w : MacIdx d N₀ M) (u : L1Torus d N₀),
      ‖((macChi d N₀ M w u : ℝ) : ℂ)‖ ≤ 1 := fun N₀ _ w u => by
    rw [Complex.norm_real, Real.norm_of_nonneg (macChi_nonneg w u)]; exact macChi_le_one w u
  refine (rowmul_close_core f hBinj t hc hc' (A := E) (A' := E')
    (β := fun _ => (2 * T * α + η * δG) * Real.exp (-σ * dist x y)) (x := x) (y := y)
    (fun u hu => ?_)).trans ?_
  · have huY : u ∈ macRegion d N M C := (hYmem u).1 (hBY hu)
    have hdxu := dist_map_eq_of_mem_macRegion hM hN hN' hf hC hx huY
    have h1 := (final_boxFamily_close_weighted hM hN hN' hf he hC hd hk hv0 hv1 ha1 ha2 hmass hU
      ht hzC huY hy).1
    rw [hBimg] at h1
    simp only [Matrix.diagonal_mul] at h1
    have h2 := norm_diag_boxG_final_le (L := L) (N := N) hd hk hv0 hv1 ha1 ha2 hmass ht
      (macBoxF d N M z) (c := fun u => ((macChi d N M z u : ℝ) : ℂ)) (hc1 N z) u y
    simp only [Matrix.diagonal_mul] at h2
    have hdu : 0 ≤ dist x u := dist_nonneg
    have hduy : 0 ≤ dist u y := dist_nonneg
    have e1 := hE.entry x u
    have e2 := hE'.entry (f x) (f u)
    rw [hdxu] at e2
    have hAd : ‖E x u - E' (f x) (f u)‖ ≤ α * Real.exp (-σ * dist x u) := by
      refine le_sqrt_mul_exp_of_le_of_le (r := rE) (A := εE) (B := 2 * η) hεE0 (by positivity) hdu
        hσr (hEc x hx u huY) ?_
      have := norm_sub_le (E x u) (E' (f x) (f u))
      linarith
    have hA'd : ‖E' (f x) (f u)‖ ≤ η * Real.exp (-σ * dist x u) :=
      e2.trans (mul_le_mul_of_nonneg_left (exp_neg_mul_anti' hdu (by linarith)) hη)
    have hXb : ‖((macChi d N M z u : ℝ) : ℂ) *
        boxG (finalOp d L N k v a) (macBoxF d N M z) t u y‖ ≤ 2 * T * Real.exp (-σ * dist u y) :=
      h2.trans (mul_le_mul_of_nonneg_left (exp_neg_mul_anti' hduy hσfr) (by positivity))
    have hXd : ‖((macChi d N M z u : ℝ) : ℂ) *
          boxG (finalOp d L N k v a) (macBoxF d N M z) t u y -
        ((macChi d N' M (e z) (f u) : ℝ) : ℂ) *
          boxG (finalOp d L N' k v a) ((macBoxF d N M z).image f) t (f u) (f y)‖ ≤
        δG * Real.exp (-σ * dist u y) :=
      h1.trans (mul_le_mul_of_nonneg_left (exp_neg_mul_anti' hduy (by rw [hσ]; linarith)) hδG0)
    rw [← hcY u (hBY hu)] at hXd
    show ‖E x u * (((macChi d N M z u : ℝ) : ℂ) *
          boxG (finalOp d L N k v a) (macBoxF d N M z) t u y) -
        E' (f x) (f u) * (((macChi d N' M (e z) (f u) : ℝ) : ℂ) *
          boxG (finalOp d L N' k v a) ((macBoxF d N M z).image f) t (f u) (f y))‖ ≤ _
    rw [← hcY u (hBY hu)]
    exact prod_close_pointwise hα0 hη (by positivity) hδG0 (Real.exp_pos _).le
      hAd hA'd hXb hXd (exp_mul_exp_le' hσ0.le (dist_triangle x u y))
  · rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hBcard hK0

/-- **Distance-weighted closeness of the tagged perturbed defect `K_E`** of the final operators on
two tori, without the factor `e^{κ |C|}`.  Under the hypotheses of `final_taggedKE_close`, with
`E`, `E'` `(rE, η)`-small for `rE ≥ pdEps / 4` and `hMκ : 8 κ 7^d ≤ pdEps d L * M`, the entries
differ at `x, y ∈ Y(C)` by at most `|C| e^{H κ} (δR + δE)`: `δR` the error of `R_z`
(`final_boxFamily_close_weighted`) and `δE` that of `E χ_z G_z` (`final_boxE_close_weighted`). -/
theorem final_taggedKE_close_weighted (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) {ε εE η rE κ : ℝ} (hκ : 0 ≤ κ)
    (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) (hrE : pdEps d L / 4 ≤ rE) (hη : 0 ≤ η)
    (hU : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤ ε)
    {E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {E' : Matrix (L1Torus d N') (L1Torus d N') ℂ}
    (hE : WSmall rE η E) (hE' : WSmall rE η E')
    (hEc : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, ‖E x y - E' (f x) (f y)‖ ≤ εE)
    {t : ℝ} (ht : 0 ≤ t)
    {s : MacIdx d N M → ℂ} (hs : s ∈ supportedOn C)
    {s' : MacIdx d N' M → ℂ} (hs' : s' ∈ supportedOn (C.image e))
    (hss : ∀ i ∈ C, s' (e i) = s i) (hsκ : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {x y : L1Torus d N} (hx : x ∈ macRegion d N M C) (hy : y ∈ macRegion d N M C) :
    ‖taggedMat Finset.univ (macTags d N M)
        (fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
            (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
          E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N k v a) (macBoxF d N M z) t)) s x y -
      taggedMat Finset.univ (macTags d N' M)
        (fun z => boxR (finalOp d L N' k v a) (macBoxF d N' M z)
            (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
          E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N' k v a) (macBoxF d N' M z) t)) s' (f x) (f y)‖ ≤
      (C.card : ℝ) * Real.exp (pdH d * κ) *
        (Real.sqrt (((((8 * M + 1) ^ d : ℕ) : ℝ) * ε * (finalGap d L + t)⁻¹ *
            (2 + (finalDecayC d L / finalGap d L + 1) * (((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2)) *
            (2 * (pdC1 d L / M) * (finalGap d L + t)⁻¹)) +
          (((8 * M + 1) ^ d : ℕ) : ℝ) *
          ((2 * (finalGap d L + t)⁻¹ * Real.sqrt (εE * (2 * η)) +
            η * Real.sqrt ((((((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2) *
              (4 * (finalGap d L + t)⁻¹)))))) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hεp := pdEps_pos (d := d) (L := L) hd
  have hσ : κ * 7 ^ d / M ≤ pdEps d L / 8 := by
    rw [div_le_iff₀ hM']
    have : (0 : ℝ) ≤ κ * 7 ^ d := by positivity
    nlinarith
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hgt : 0 < finalGap d L + t := by linarith
  have hT0 : 0 < (finalGap d L + t)⁻¹ := inv_pos.2 hgt
  refine (taggedMat_close_twoTorus_weighted_le hM hN hN' hf he hC hκ (by positivity) hσ
    (δ := Real.sqrt (((((8 * M + 1) ^ d : ℕ) : ℝ) * ε * (finalGap d L + t)⁻¹ *
            (2 + (finalDecayC d L / finalGap d L + 1) * (((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2)) *
            (2 * (pdC1 d L / M) * (finalGap d L + t)⁻¹)) +
          (((8 * M + 1) ^ d : ℕ) : ℝ) *
          ((2 * (finalGap d L + t)⁻¹ * Real.sqrt (εE * (2 * η)) +
            η * Real.sqrt ((((((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2) *
              (4 * (finalGap d L + t)⁻¹)))))) (σ := pdEps d L / 8)
    (a := fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
            (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
          E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N k v a) (macBoxF d N M z) t))
    (a' := fun z => boxR (finalOp d L N' k v a) (macBoxF d N' M z)
            (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
          E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N' k v a) (macBoxF d N' M z) t))
    (fun z hzC u hu w hw => ?_) hs hs' hss hsκ hx hy).trans (le_of_eq rfl)
  have h1 := (final_boxFamily_close_weighted hM hN hN' hf he hC hd hk hv0 hv1 ha1 ha2 hmass hU ht
    hzC hu hw).2
  have h2 := final_boxE_close_weighted hM hN hN' hf he hC hd hk hv0 hv1 ha1 ha2 hmass hrE hη hU hE hE'
    hEc ht hzC hu hw
  have hdu : 0 ≤ dist u w := dist_nonneg
  have h1' := h1.trans (mul_le_mul_of_nonneg_left (exp_neg_mul_anti' hdu
    (by linarith : pdEps d L / 8 ≤ pdEps d L / 4)) (Real.sqrt_nonneg _))
  have : (boxR (finalOp d L N k v a) (macBoxF d N M z) (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
        E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N k v a) (macBoxF d N M z) t)) u w -
      (boxR (finalOp d L N' k v a) (macBoxF d N' M (e z))
          (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) t -
        E' * (Matrix.diagonal (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) *
          boxG (finalOp d L N' k v a) (macBoxF d N' M (e z)) t)) (f u) (f w) =
      (boxR (finalOp d L N k v a) (macBoxF d N M z) (fun u => ((macChi d N M z u : ℝ) : ℂ)) t u w -
        boxR (finalOp d L N' k v a) (macBoxF d N' M (e z))
          (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) t (f u) (f w)) -
      ((E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N k v a) (macBoxF d N M z) t)) u w -
        (E' * (Matrix.diagonal (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) *
          boxG (finalOp d L N' k v a) (macBoxF d N' M (e z)) t)) (f u) (f w)) := by
    simp only [Matrix.sub_apply]; ring
  show ‖(boxR (finalOp d L N k v a) (macBoxF d N M z) (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
        E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N k v a) (macBoxF d N M z) t)) u w -
      (boxR (finalOp d L N' k v a) (macBoxF d N' M (e z))
          (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) t -
        E' * (Matrix.diagonal (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) *
          boxG (finalOp d L N' k v a) (macBoxF d N' M (e z)) t)) (f u) (f w)‖ ≤ _
  rw [this]
  refine (norm_sub_le _ _).trans ?_
  calc _ ≤ _ := add_le_add h1' h2
    _ = _ := by ring

end TwoTorus

/-- Simplification of the error of the tagged perturbed defect: for `0 ≤ T ≤ g⁻¹` the error
terms of `final_taggedKE_close_weighted` are at most `cK (√ε + √εE)`, where `cK` depends on
`nB`, `P0`, `c`, `η` and `g` only. -/
theorem weighted_defect_err_le {nB ε εE η T c P0 g : ℝ} (hnB : 0 ≤ nB) (hε : 0 ≤ ε)
    (hεE : 0 ≤ εE) (hη : 0 ≤ η) (hT : 0 < T) (hg : 0 < g) (hTg : T ≤ g⁻¹) (hc : 0 ≤ c)
    (hP0 : 0 ≤ P0) :
    Real.sqrt ((nB * ε * T * (2 + P0 * nB ^ 2)) * (2 * c * T)) +
        nB * (2 * T * Real.sqrt (εE * (2 * η)) +
          η * Real.sqrt ((nB ^ 2 * ε * T ^ 2) * (4 * T))) ≤
      (g⁻¹ * Real.sqrt (2 * c * (nB * (2 + P0 * nB ^ 2))) + 2 * nB * g⁻¹ * Real.sqrt (2 * η) +
          2 * nB ^ 2 * η * g⁻¹ * (Real.sqrt g)⁻¹) * (Real.sqrt ε + Real.sqrt εE) := by
  have hK0 : 0 ≤ 2 * c * (nB * (2 + P0 * nB ^ 2)) := by positivity
  have hsq0 := Real.sqrt_nonneg ε
  have hsqE0 := Real.sqrt_nonneg εE
  have hgi : 0 < g⁻¹ := inv_pos.2 hg
  have hsg : 0 < (Real.sqrt g)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hg)
  have b1 := sqrt_boxR_err_le (nB := nB) (ε := ε) (T := T) (c := c) (P0 := P0) hε hT hK0
  have b2 := sqrt_boxG_err_le (nB := nB) (ε := ε) (T := T) (g := g) hnB hε hT hg hTg
  have b3 : Real.sqrt (εE * (2 * η)) = Real.sqrt εE * Real.sqrt (2 * η) :=
    Real.sqrt_mul hεE _
  have hs2 : 0 ≤ Real.sqrt (2 * η) := Real.sqrt_nonneg _
  have hsK : 0 ≤ Real.sqrt (2 * c * (nB * (2 + P0 * nB ^ 2))) := Real.sqrt_nonneg _
  have c1 : Real.sqrt ε * T * Real.sqrt (2 * c * (nB * (2 + P0 * nB ^ 2))) ≤
      g⁻¹ * Real.sqrt (2 * c * (nB * (2 + P0 * nB ^ 2))) * Real.sqrt ε := by
    have := mul_le_mul_of_nonneg_right hTg (mul_nonneg hsq0 hsK)
    nlinarith
  have c2 : nB * (2 * T * Real.sqrt (εE * (2 * η))) ≤
      2 * nB * g⁻¹ * Real.sqrt (2 * η) * Real.sqrt εE := by
    rw [b3]
    have := mul_le_mul_of_nonneg_right hTg (mul_nonneg hsqE0 hs2)
    nlinarith [mul_nonneg hnB (mul_nonneg hsqE0 hs2)]
  have c3 : nB * (η * Real.sqrt ((nB ^ 2 * ε * T ^ 2) * (4 * T))) ≤
      2 * nB ^ 2 * η * g⁻¹ * (Real.sqrt g)⁻¹ * Real.sqrt ε := by
    have h1 : η * Real.sqrt ((nB ^ 2 * ε * T ^ 2) * (4 * T)) ≤
        η * (2 * nB * Real.sqrt ε * g⁻¹ * (Real.sqrt g)⁻¹) :=
      mul_le_mul_of_nonneg_left (b2.trans (by
        have := mul_le_mul_of_nonneg_right hTg (by positivity :
          0 ≤ 2 * nB * Real.sqrt ε * (Real.sqrt g)⁻¹)
        nlinarith)) hη
    calc _ ≤ nB * (η * (2 * nB * Real.sqrt ε * g⁻¹ * (Real.sqrt g)⁻¹)) :=
          mul_le_mul_of_nonneg_left h1 hnB
      _ = _ := by ring
  have hA : 0 ≤ g⁻¹ * Real.sqrt (2 * c * (nB * (2 + P0 * nB ^ 2))) * Real.sqrt εE := by positivity
  have hB : 0 ≤ 2 * nB * g⁻¹ * Real.sqrt (2 * η) * Real.sqrt ε := by positivity
  have hC : 0 ≤ 2 * nB ^ 2 * η * g⁻¹ * (Real.sqrt g)⁻¹ * Real.sqrt εE := by positivity
  nlinarith [b1, c1, c2, c3, hA, hB, hC]

section Unif

variable {d M L : ℕ} [NeZero L]

/-- **The localized coefficients of the logarithm of the perturbed defect on two tori, polynomial
in the number of cells (blocker 7, weighted).**  As `final_coef_logdet_close_twoTorus_unif`, with
the constant `P` independent of the bound `nC ≥ |C|` of the number of cells: the bound is
`P nC³ (√ε₀ + √εE) / (e^κ - 1)^{|C|}`, `ε₀ = C₀ exp(-c₀ (min N N'/2 - (J+3) M))`; there is no
factor `e^{κ nC}`.  The price is the square roots, from the interpolation with the decay of the
entries (`final_taggedKE_close_weighted`). -/
theorem final_coef_logdet_close_twoTorus_unif_weighted (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 0 < κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {rE η : ℝ} (hrE : pdEps d L / 4 ≤ rE) (hη0 : 0 ≤ η)
    (hη : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η *
      ballConst d (3 * pdEps d L / 4))) ≤ 1)
    :
    ∃ P C₀ c₀ : ℝ, 0 ≤ P ∧ 0 < C₀ ∧ 0 < c₀ ∧ ∀ (nC : ℕ) {k : ℕ}, 1 ≤ k →
      ∀ {J N N' : ℕ} [NeZero N] [NeZero N'], 2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' →
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {t : ℝ}, 0 ≤ t →
      ∀ {E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {E' : Matrix (L1Torus d N') (L1Torus d N') ℂ},
      WSmall rE η E → WSmall rE η E' → ∀ {εE : ℝ}, 0 ≤ εE →
      (∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, ‖E x y - E' (f x) (f y)‖ ≤ εE) →
      ∀ {ρ ρ' : ℝ}, Real.exp κ < ρ → Real.exp κ < ρ' →
      ∀ {ell : (MacIdx d N M → ℂ) → ℂ} {ell' : (MacIdx d N' M → ℂ) → ℂ},
      AnalyticOnNhd ℂ ell (Metric.ball 0 ρ) → AnalyticOnNhd ℂ ell' (Metric.ball 0 ρ') →
      ell 0 = 0 → ell' 0 = 0 →
      (∀ s ∈ Metric.ball (0 : MacIdx d N M → ℂ) ρ,
        (1 - taggedMat Finset.univ (macTags d N M)
          (fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
              (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N k v a) (macBoxF d N M z) t)) s).det =
          Complex.exp (ell s)) →
      (∀ s ∈ Metric.ball (0 : MacIdx d N' M → ℂ) ρ',
        (1 - taggedMat Finset.univ (macTags d N' M)
          (fun z => boxR (finalOp d L N' k v a) (macBoxF d N' M z)
              (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
            E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N' k v a) (macBoxF d N' M z) t)) s).det =
          Complex.exp (ell' s)) →
      ‖coef ell C - coef ell' (C.image e)‖ ≤
        P * (nC : ℝ) ^ 3 * (Real.sqrt (C₀ * Real.exp (-c₀ *
            (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ)))) + Real.sqrt εE) /
          (Real.exp κ - 1) ^ C.card := by
  classical
  obtain ⟨C₀, c₀, hC₀, hc₀, hreg⟩ := final_region_entry_close_unif (L := L) hd
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hA0 := finalDecayC_pos (L := L) hd
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hε := pdEps_pos (d := d) (L := L) hd
  have hC1 : 0 ≤ pdC1 d L := by
    unfold pdC1 pdLip
    have := ballConst_nonneg (d := d) (r := pdEps d L / 4) (by positivity)
    positivity
  set nB : ℝ := (((8 * M + 1) ^ d : ℕ) : ℝ) with hnBdef
  have hnB : 0 ≤ nB := by positivity
  set Hk : ℝ := Real.exp (pdH d * κ) with hHk
  have hHk0 : 0 < Hk := Real.exp_pos _
  set P0 : ℝ := finalDecayC d L / finalGap d L + 1 with hP0
  have hP00 : 0 ≤ P0 := by positivity
  set c : ℝ := pdC1 d L / M with hc
  have hc0 : 0 ≤ c := by positivity
  set cK : ℝ := (finalGap d L)⁻¹ * Real.sqrt (2 * c * (nB * (2 + P0 * nB ^ 2))) +
    2 * nB * (finalGap d L)⁻¹ * Real.sqrt (2 * η) +
    2 * nB ^ 2 * η * (finalGap d L)⁻¹ * (Real.sqrt (finalGap d L))⁻¹ with hcK
  have hcK0 : 0 ≤ cK := by positivity
  refine ⟨2 * nB ^ 2 * Hk * cK, C₀, c₀, by positivity, hC₀, hc₀, ?_⟩
  intro nC k hk J N N' _ _ hN hN' f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass t ht E E' hE hE' εE
    hεE0 hEc ρ ρ' hρ hρ' ell ell' hell hell' h0 h0' hdet hdet'
  set ε₀ : ℝ := C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ)))
    with hε₀
  have hε00 : 0 ≤ ε₀ := by positivity
  have hU : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤ ε₀ :=
    fun x hx y hy => hreg hk hv0 hv1 ha1 ha2 hmass hM hN hN' hf hC x hx y hy
  have hnC0 : (0 : ℝ) ≤ nC := Nat.cast_nonneg _
  have hCc' : (C.card : ℝ) ≤ nC := by exact_mod_cast hCc
  have hsum0 : 0 ≤ Real.sqrt ε₀ + Real.sqrt εE := by positivity
  have key := final_coef_logdet_close_core hd hM hκ hMB hMκ hrE hη nC hk hN hN' hf he hCc hC hv0
    hv1 ha1 ha2 hmass ht hE hE' hρ hρ' hell hell' h0 h0' hdet hdet'
    (δ0 := nC * Hk * (cK * (Real.sqrt ε₀ + Real.sqrt εE))) (by positivity) ?_
  · refine key.trans (le_of_eq ?_)
    rw [hnBdef]
    ring
  · intro s hs s' hs' hss hsκ x y hx hy
    have h := final_taggedKE_close_weighted hM hN hN' hf he hC hd hk hv0 hv1 ha1 ha2 hmass hκ.le
      hMκ hrE hη0 hU hE hE' hEc ht hs hs' hss hsκ hx hy
    refine h.trans ?_
    have hgt : 0 < finalGap d L + t := by linarith
    have hT0 : 0 < (finalGap d L + t)⁻¹ := inv_pos.2 hgt
    have hTg : (finalGap d L + t)⁻¹ ≤ (finalGap d L)⁻¹ := inv_anti₀ hg (by linarith)
    have hb := weighted_defect_err_le (nB := nB) (ε := ε₀) (εE := εE) (η := η)
      (T := (finalGap d L + t)⁻¹) (c := c) (P0 := P0) (g := finalGap d L) hnB hε00 hεE0 hη0 hT0
      hg hTg hc0 hP00
    calc _ ≤ (C.card : ℝ) * Hk * (cK * (Real.sqrt ε₀ + Real.sqrt εE)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ nC * Hk * (cK * (Real.sqrt ε₀ + Real.sqrt εE)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCc' hHk0.le) (by positivity)

end Unif

end Balaban.Green
