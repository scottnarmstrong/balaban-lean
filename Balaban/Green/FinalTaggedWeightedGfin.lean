/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTaggedWeighted
public import Balaban.Green.FinalTaggedTorusClose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Distance-weighted closeness of the box families and of the tagged parametrix (blocker 7)

Continuation of `Green/FinalTaggedWeighted`.  The box families `χ_z G_z` and the defects `R_z` of
the final operators on two tori are close up to a small error `ε` on `Y(C)²`
(`final_boxFamily_close`).  Both families also decay in `dist(x, y)`: `χ_z G_z` at the rate
`finalRate d L` (`boxG_final_entry_bound`), `R_z` at the rate `pdEps d L / 2`
(`boxR_final_entry_bound`).  Interpolating (`min_le_sqrt_mul_exp`) the entry differences are at most
`δ e^{-(pdEps/4) dist(x, y)}` with `δ` of order `√ε` (`final_boxFamily_close_weighted`).

With `σ = pdEps d L / 4`, the condition `κ 7^d / M ≤ σ` of
`taggedMat_close_twoTorus_weighted_le` follows from `hMκ : 8 κ 7^d ≤ pdEps d L * M`.  Hence the
tagged `G_*` and `K` differ by at most `|C| e^{H κ} δ` (`final_taggedGK_close_weighted`), with no
factor `e^{κ |C|}`, and the entries of `G_fin` and of `taggedCfinU` by `P (nC² + nC⁴) √ε …` with `P`
independent of the number `nC ≥ |C|` of cells (`final_taggedGfin_close_weighted`,
`final_taggedCfinU_close_weighted`), through the shared cores `final_taggedGfin_close_core` and
`taggedCfinU_close_of_Gfin`.
-/

@[expose] public section

open Finset Matrix Balaban.Localization

namespace Balaban.Green

/-- Interpolation of an absolute and a decaying bound: if `P ≤ A`, `P ≤ B e^{-r t}` and
`s ≤ r / 2`, then `P ≤ √(A B) e^{-s t}`. -/
theorem le_sqrt_mul_exp_of_le_of_le {P A B r s t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hs : s ≤ r / 2) (hP1 : P ≤ A) (hP2 : P ≤ B * Real.exp (-r * t)) :
    P ≤ Real.sqrt (A * B) * Real.exp (-s * t) := by
  refine ((le_min hP1 hP2).trans (min_le_sqrt_mul_exp hA hB)).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.sqrt_nonneg _)
  nlinarith

section TwoTorus

variable {d L k M J N N' : ℕ} [NeZero N] [NeZero N'] [NeZero L]

/-- The cut-off box resolvent `χ G` of the final operator decays at the rate `finalRate`. -/
theorem norm_diag_boxG_final_le (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (B : Finset (L1Torus d N)) {c : L1Torus d N → ℂ}
    (hc : ∀ u, ‖c u‖ ≤ 1) (x y : L1Torus d N) :
    ‖(Matrix.diagonal c * boxG (finalOp d L N k v a) B t) x y‖ ≤
      2 * (finalGap d L + t)⁻¹ * Real.exp (-finalRate d L * dist x y) := by
  rw [Matrix.diagonal_mul, norm_mul]
  have h := boxG_final_entry_bound hd hk hv0 hv1 ha1 ha2 hmass ht B x y
  rw [div_eq_mul_inv] at h
  calc ‖c x‖ * _ ≤ 1 * (2 * (finalGap d L + t)⁻¹ * Real.exp (-finalRate d L * dist x y)) :=
        mul_le_mul (hc x) h (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- **Distance-weighted closeness of the box resolvent family of the final operators on two
tori.**  Under the hypotheses of `final_boxFamily_close` (the entries of the final operators differ
by at most `ε` on `Y(C)²`), for a cell `z ∈ C` and `x, y ∈ Y(C)` the entries of `χ_z G_z` and of
the defect `R_z` differ by at most `δ e^{-(pdEps/4) dist(x, y)}`, where, with `T = (g + t)⁻¹`,
`nB = (8M+1)^d`, `P₀ = A / g + 1`, `A = finalDecayC d L`,
`δ = √(nB² ε T² · 4T)` for `χ_z G_z` and `δ = √(nB ε T (2 + P₀ nB²) · 2 (C₁ / M) T)` for `R_z`
(`C₁ = pdC1 d L`). -/
theorem final_boxFamily_close_weighted (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) {ε : ℝ}
    (hU : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤ ε)
    {t : ℝ} (ht : 0 ≤ t) {z : MacIdx d N M} (hzC : z ∈ C) {x y : L1Torus d N}
    (hx : x ∈ macRegion d N M C) (hy : y ∈ macRegion d N M C) :
    ‖(Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N k v a) (macBoxF d N M z) t) x y -
        (Matrix.diagonal (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) *
          boxG (finalOp d L N' k v a) (macBoxF d N' M (e z)) t) (f x) (f y)‖ ≤
      Real.sqrt ((((((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2) *
          (4 * (finalGap d L + t)⁻¹))) * Real.exp (-(pdEps d L / 4) * dist x y) ∧
    ‖boxR (finalOp d L N k v a) (macBoxF d N M z) (fun u => ((macChi d N M z u : ℝ) : ℂ)) t x y -
        boxR (finalOp d L N' k v a) (macBoxF d N' M (e z))
          (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) t (f x) (f y)‖ ≤
      Real.sqrt (((((8 * M + 1) ^ d : ℕ) : ℝ) * ε * (finalGap d L + t)⁻¹ *
          (2 + (finalDecayC d L / finalGap d L + 1) * (((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2)) *
          (2 * (pdC1 d L / M) * (finalGap d L + t)⁻¹)) *
        Real.exp (-(pdEps d L / 4) * dist x y) := by
  classical
  obtain ⟨h1, h2⟩ := final_boxFamily_close hM hN hN' hf he hC hd hk hv0 hv1 ha1 ha2 hmass hU ht
    hzC hx hy
  have hdist := dist_map_eq_of_mem_macRegion hM hN hN' hf hC hx hy
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hU x hx y hy)
  have hgt : 0 < finalGap d L + t := by linarith
  have hT0 : 0 < (finalGap d L + t)⁻¹ := inv_pos.2 hgt
  have hε := pdEps_pos (d := d) (L := L) hd
  have hr : pdEps d L ≤ finalRate d L := min_le_right _ _
  have hdx : 0 ≤ dist x y := dist_nonneg
  have hA0 := finalDecayC_pos (L := L) hd
  have hc1 : ∀ (N₀ : ℕ) [NeZero N₀] (w : MacIdx d N₀ M) (u : L1Torus d N₀),
      ‖((macChi d N₀ M w u : ℝ) : ℂ)‖ ≤ 1 := fun N₀ _ w u => by
    rw [Complex.norm_real, Real.norm_of_nonneg (macChi_nonneg w u)]; exact macChi_le_one w u
  have hnB : 0 ≤ (((8 * M + 1) ^ d : ℕ) : ℝ) := by positivity
  have hC1 : 0 ≤ pdC1 d L := by
    unfold pdC1 pdLip
    have := ballConst_nonneg (d := d) (r := pdEps d L / 4) (by positivity)
    positivity
  refine ⟨?_, ?_⟩
  · have e1 := norm_diag_boxG_final_le (L := L) (N := N) hd hk hv0 hv1 ha1 ha2 hmass ht
      (macBoxF d N M z) (c := fun u => ((macChi d N M z u : ℝ) : ℂ)) (hc1 N z) x y
    have e2 := norm_diag_boxG_final_le (L := L) (N := N') hd hk hv0 hv1 ha1 ha2 hmass ht
      (macBoxF d N' M (e z)) (c := fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) (hc1 N' (e z))
      (f x) (f y)
    rw [hdist] at e2
    refine le_sqrt_mul_exp_of_le_of_le (r := finalRate d L) (by positivity) (by positivity) hdx
      (by linarith) h1 ((norm_sub_le _ _).trans ?_)
    nlinarith
  · have e1 := boxR_final_entry_bound (L := L) (N₀ := N) (k := k) hd hk hv0 hv1 ha1 ha2 hmass ht
      hM z x y
    have e2 := boxR_final_entry_bound (L := L) (N₀ := N') (k := k) hd hk hv0 hv1 ha1 ha2 hmass ht
      hM (e z) (f x) (f y)
    rw [hdist] at e2
    have hpos : 0 ≤ (((8 * M + 1) ^ d : ℕ) : ℝ) * ε * (finalGap d L + t)⁻¹ *
        (2 + (finalDecayC d L / finalGap d L + 1) * (((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2) := by
      positivity
    refine le_sqrt_mul_exp_of_le_of_le (r := pdEps d L / 2) hpos (by positivity) hdx
      (by linarith) h2 ((norm_sub_le _ _).trans ?_)
    rw [one_div] at e1 e2
    nlinarith

/-- **Closeness of the tagged `G_*` and the tagged defect `K` of the final operators on two tori,
without the factor `e^{κ |C|}`.**  Under the hypotheses of `final_taggedGK_close` and
`hMκ : 8 κ 7^d ≤ pdEps d L * M`, the entries of the tagged `G_*` (resp. `K`) differ at
`x, y ∈ Y(C)` by at most `|C| e^{H κ}` times the error `δ` of `final_boxFamily_close_weighted`
for `χ_z G_z` (resp. `R_z`).  The rate is `σ = pdEps d L / 4`; the condition
`κ 7^d / M ≤ σ` of `taggedMat_close_twoTorus_weighted_le` follows from `hMκ`. -/
theorem final_taggedGK_close_weighted (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) {ε κ : ℝ} (hκ : 0 ≤ κ)
    (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (hU : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤ ε)
    {t : ℝ} (ht : 0 ≤ t)
    {s : MacIdx d N M → ℂ} (hs : s ∈ supportedOn C)
    {s' : MacIdx d N' M → ℂ} (hs' : s' ∈ supportedOn (C.image e))
    (hss : ∀ i ∈ C, s' (e i) = s i) (hsκ : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {x y : L1Torus d N} (hx : x ∈ macRegion d N M C) (hy : y ∈ macRegion d N M C) :
    ‖taggedG Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
          (macTags d N M) (finalOp d L N k v a) t s x y -
        taggedG Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
          (macTags d N' M) (finalOp d L N' k v a) t s' (f x) (f y)‖ ≤
      (C.card : ℝ) * Real.exp (pdH d * κ) *
        Real.sqrt ((((((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2) *
          (4 * (finalGap d L + t)⁻¹))) ∧
    ‖taggedK Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
          (macTags d N M) (finalOp d L N k v a) t s x y -
        taggedK Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
          (macTags d N' M) (finalOp d L N' k v a) t s' (f x) (f y)‖ ≤
      (C.card : ℝ) * Real.exp (pdH d * κ) *
        Real.sqrt (((((8 * M + 1) ^ d : ℕ) : ℝ) * ε * (finalGap d L + t)⁻¹ *
          (2 + (finalDecayC d L / finalGap d L + 1) * (((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2)) *
          (2 * (pdC1 d L / M) * (finalGap d L + t)⁻¹)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hε := pdEps_pos (d := d) (L := L) hd
  have hσ : κ * 7 ^ d / M ≤ pdEps d L / 4 := by
    rw [div_le_iff₀ hM']
    have : (0 : ℝ) ≤ κ * 7 ^ d := by positivity
    nlinarith
  refine ⟨?_, ?_⟩
  · unfold taggedG
    exact taggedMat_close_twoTorus_weighted_le hM hN hN' hf he hC hκ (by positivity) hσ
      (fun z hzC u hu w hw => (final_boxFamily_close_weighted hM hN hN' hf he hC hd hk hv0 hv1 ha1
        ha2 hmass hU ht hzC hu hw).1) hs hs' hss hsκ hx hy
  · unfold taggedK
    exact taggedMat_close_twoTorus_weighted_le hM hN hN' hf he hC hκ (by positivity) hσ
      (fun z hzC u hu w hw => (final_boxFamily_close_weighted hM hN hN' hf he hC hd hk hv0 hv1 ha1
        ha2 hmass hU ht hzC hu hw).2) hs hs' hss hsκ hx hy

end TwoTorus

/-- The error of `χ_z G_z` is at most `2 nB √ε T / √g`. -/
theorem sqrt_boxG_err_le {nB ε T g : ℝ} (hnB : 0 ≤ nB) (hε : 0 ≤ ε) (hT : 0 < T) (hg : 0 < g)
    (hTg : T ≤ g⁻¹) :
    Real.sqrt ((nB ^ 2 * ε * T ^ 2) * (4 * T)) ≤ 2 * nB * Real.sqrt ε * T * (Real.sqrt g)⁻¹ := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : (2 * nB * Real.sqrt ε * T * (Real.sqrt g)⁻¹) ^ 2 = 4 * nB ^ 2 * ε * T ^ 2 * g⁻¹ := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hε, Real.sq_sqrt hg.le]
    ring
  rw [h1]
  have h2 : 0 ≤ 4 * nB ^ 2 * ε * T ^ 2 := by positivity
  calc (nB ^ 2 * ε * T ^ 2) * (4 * T) = 4 * nB ^ 2 * ε * T ^ 2 * T := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hTg h2

/-- The error of `R_z` is at most `√ε T √K`. -/
theorem sqrt_boxR_err_le {nB ε T c P0 : ℝ} (hε : 0 ≤ ε) (hT : 0 < T) (hK : 0 ≤ 2 * c * (nB * (2 + P0 * nB ^ 2))) :
    Real.sqrt ((nB * ε * T * (2 + P0 * nB ^ 2)) * (2 * c * T)) ≤
      Real.sqrt ε * T * Real.sqrt (2 * c * (nB * (2 + P0 * nB ^ 2))) := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, mul_pow, Real.sq_sqrt hε, Real.sq_sqrt hK]
  ring_nf
  exact le_rfl

section TwoTorus

variable {d L M : ℕ} [NeZero L]

/-- **Closeness of the tagged parametrix `G_fin` of the final operators on two tori, polynomial in
the number of cells.**  Under the hypotheses of `final_taggedGfin_close` (`hMB`, `hMκ`; the entries
of the operators differ by at most `ε` on `Y(C)²`), the entries of `G_fin(s, t)` differ at
`x, y ∈ Y(C)` by at most `P (nC² + nC⁴) √ε (g + t)⁻¹`, for every `nC ≥ |C|`.  The constant `P`
depends on `d`, `L`, `M`, `κ` only (not on `nC`, `k`, the window, the sides or `t`), and there is no
factor `e^{κ nC}`: the tag monomials are bounded through the distance decay
(`taggedMat_close_twoTorus_weighted_le`).  The price is `√ε` instead of `ε`. -/
theorem final_taggedGfin_close_weighted (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (nC : ℕ) {k J N N' : ℕ} [NeZero N] [NeZero N'], 1 ≤ k →
      2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' → ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {ε : ℝ}, (∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
        ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤ ε) →
      ∀ {t : ℝ}, 0 ≤ t →
      ∀ {s : MacIdx d N M → ℂ}, s ∈ supportedOn C →
      ∀ {s' : MacIdx d N' M → ℂ}, s' ∈ supportedOn (C.image e) →
      (∀ i ∈ C, s' (e i) = s i) → (∀ p, ‖s p‖ ≤ Real.exp κ) →
      ∀ {x y : L1Torus d N}, x ∈ macRegion d N M C → y ∈ macRegion d N M C →
      ‖taggedGfin Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
            (macTags d N M) (finalOp d L N k v a) t s x y -
          taggedGfin Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
            (macTags d N' M) (finalOp d L N' k v a) t s' (f x) (f y)‖ ≤
        P * ((nC : ℝ) ^ 2 + (nC : ℝ) ^ 4) * Real.sqrt ε * (finalGap d L + t)⁻¹ := by
  classical
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
  have hK0 : 0 ≤ 2 * c * (nB * (2 + P0 * nB ^ 2)) := by positivity
  set sq : ℝ := Real.sqrt (2 * c * (nB * (2 + P0 * nB ^ 2))) with hsq
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  set w : ℝ := Real.sqrt (finalGap d L) with hw
  have hw0 : 0 < w := Real.sqrt_pos.2 hg
  refine ⟨(8 / 3) * nB ^ 2 * Hk * w⁻¹ + (32 / 9) * nB ^ 3 * Hk ^ 2 * sq * (finalGap d L)⁻¹,
    by positivity, ?_⟩
  intro nC k J N N' _ _ hk hN hN' f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass ε hU t ht s hs s' hs'
    hss hsκ x y hx hy
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hU x hx y hy)
  have hgt : 0 < finalGap d L + t := by linarith
  set T : ℝ := (finalGap d L + t)⁻¹ with hT
  have hT0 : 0 < T := inv_pos.2 hgt
  have hTg : T ≤ (finalGap d L)⁻¹ := inv_anti₀ hg (by linarith)
  set r : ℝ := Real.sqrt ε with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hnC0 : (0 : ℝ) ≤ nC := Nat.cast_nonneg _
  have hCc' : (C.card : ℝ) ≤ nC := by exact_mod_cast hCc
  set δ1 : ℝ := 2 * nB * r * T * w⁻¹ with hδ1
  set δ2 : ℝ := r * T * sq with hδ2
  have hδ10 : 0 ≤ δ1 := by positivity
  have hδ20 : 0 ≤ δ2 := by positivity
  have hGK := fun p (hp : p ∈ macRegion d N M C) q (hq : q ∈ macRegion d N M C) =>
    final_taggedGK_close_weighted hM hN hN' hf he hC hd hk hv0 hv1 ha1 ha2 hmass hκ hMκ hU ht hs hs'
      hss hsκ hp hq
  have hb1 := sqrt_boxG_err_le (nB := nB) (T := T) (g := finalGap d L) hnB hε0 hT0 hg hTg
  have hb2 := sqrt_boxR_err_le (nB := nB) (ε := ε) (T := T) (c := c) (P0 := P0) hε0 hT0 hK0
  have hCe : (C.card : ℝ) * Hk ≤ nC * Hk := mul_le_mul_of_nonneg_right hCc' hHk0.le
  have hcore := final_taggedGfin_close_core (nC := nC) hd hM hκ hMB hMκ hk hN hN' hf he hCc hC hv0
    hv1 ha1 ha2 hmass ht hs hs' hss hsκ hx hy (δG := nC * Hk * δ1) (δK := nC * Hk * δ2)
    (by positivity) (by positivity)
    (fun p hp q hq => ((hGK p hp q hq).1).trans
      (mul_le_mul hCe hb1 (Real.sqrt_nonneg _) (by positivity)))
    (fun p hp q hq => ((hGK p hp q hq).2).trans
      (mul_le_mul hCe hb2 (Real.sqrt_nonneg _) (by positivity)))
  refine hcore.trans ?_
  have hwinv : 0 ≤ w⁻¹ := by positivity
  have e1 : ((nC : ℝ) * nB) * (nC * Hk * δ1 * (4 / 3)) =
      ((8 / 3) * nB ^ 2 * Hk * w⁻¹) * (nC : ℝ) ^ 2 * r * T := by
    rw [hδ1]; ring
  have e2 : ((nC : ℝ) * nB) ^ 3 * (2 * Hk * T * (4 / 3 * (4 / 3 * (nC * Hk * δ2)))) =
      ((32 / 9) * nB ^ 3 * Hk ^ 2 * sq) * (nC : ℝ) ^ 4 * r * T * T := by
    rw [hδ2]; ring
  have e3 : ((32 / 9) * nB ^ 3 * Hk ^ 2 * sq) * (nC : ℝ) ^ 4 * r * T * T ≤
      ((32 / 9) * nB ^ 3 * Hk ^ 2 * sq * (finalGap d L)⁻¹) * (nC : ℝ) ^ 4 * r * T := by
    have h0 : 0 ≤ ((32 / 9) * nB ^ 3 * Hk ^ 2 * sq) * (nC : ℝ) ^ 4 * r * T := by positivity
    calc _ = (((32 / 9) * nB ^ 3 * Hk ^ 2 * sq) * (nC : ℝ) ^ 4 * r * T) * T := rfl
      _ ≤ (((32 / 9) * nB ^ 3 * Hk ^ 2 * sq) * (nC : ℝ) ^ 4 * r * T) * (finalGap d L)⁻¹ :=
          mul_le_mul_of_nonneg_left hTg h0
      _ = _ := by ring
  rw [e1, e2]
  have hp1 : 0 ≤ ((8 / 3) * nB ^ 2 * Hk * w⁻¹) * (nC : ℝ) ^ 2 * r * T := by positivity
  have hp2 : 0 ≤ ((32 / 9) * nB ^ 3 * Hk ^ 2 * sq * (finalGap d L)⁻¹) * (nC : ℝ) ^ 4 * r * T := by
    positivity
  have hq1 : 0 ≤ ((8 / 3) * nB ^ 2 * Hk * w⁻¹) * (nC : ℝ) ^ 4 * r * T := by positivity
  have hq2 : 0 ≤ ((32 / 9) * nB ^ 3 * Hk ^ 2 * sq * (finalGap d L)⁻¹) * (nC : ℝ) ^ 2 * r * T := by
    positivity
  have hexp : ((8 / 3) * nB ^ 2 * Hk * w⁻¹ + (32 / 9) * nB ^ 3 * Hk ^ 2 * sq * (finalGap d L)⁻¹) *
      ((nC : ℝ) ^ 2 + (nC : ℝ) ^ 4) * r * T =
      ((8 / 3) * nB ^ 2 * Hk * w⁻¹) * (nC : ℝ) ^ 2 * r * T +
      ((32 / 9) * nB ^ 3 * Hk ^ 2 * sq * (finalGap d L)⁻¹) * (nC : ℝ) ^ 4 * r * T +
      (((8 / 3) * nB ^ 2 * Hk * w⁻¹) * (nC : ℝ) ^ 4 * r * T +
        ((32 / 9) * nB ^ 3 * Hk ^ 2 * sq * (finalGap d L)⁻¹) * (nC : ℝ) ^ 2 * r * T) := by
    ring
  rw [hexp]
  linarith

end TwoTorus

end Balaban.Green
