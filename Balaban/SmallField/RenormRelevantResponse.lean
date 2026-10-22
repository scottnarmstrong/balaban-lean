/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormRelevantConst
public import Balaban.Background.Theorem52Analytic

/-!
# The first-order response of the background at the constant datum

For a whole-lattice level, the datum `Ψ_s = e + s ψ'`, `h̃ = e` with a layer-constant transverse
perturbation `ψ'` (`e · ψ' = 0`) lies in the complex union domain for small `|s|`, and the background
`(bgFieldC, bgMultC)` of `Ψ_s` is differentiable at `s = 0` (`theorem52_analytic`).  Differentiating (EL) at
the constant solution `(e, 0)` gives the first-order response (P4 (5.8), at `λ = ∞`):
`H_0 φ¹ = a Q* ψ'`, `e · φ¹ = 0`, `α¹ = 0`, i.e. `φ¹ = a G Q* ψ'` with `G = (−Δ + aQ*Q + ν)^{-1}`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Matrix

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {n : ℕ}

theorem BgData.ext' {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ) (hh : D.h = D'.h) : D = D' := by
  cases D; cases D'; simp only at hΨ hh; subst hΨ; subst hh; rfl

/-- The line of data `Ψ_s = e + s ψ'`, `h̃ = e`. -/
noncomputable def lineBg (hG : IsLevel G n) (e : Fin N → ℂ) (ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hψ' : IsLayerConstant G ψ') (s : ℂ) : BgData G N where
  Ψ := fun x i => e i + s * ψ' x i
  h := fun _ => e
  Ψ_layerConst := fun m hm1 hmk x hx x' hx' => by
    funext i; simp only [hψ' m hm1 hmk x hx x' hx']
  h_layerConst := fun _ _ _ _ _ _ _ => rfl
  Ψ_zero := fun x hx => absurd (by rw [hG.dataSites_eq]; exact Finset.mem_univ x) hx
  h_zero := fun x hx => absurd (hG x).1 hx

theorem lineBg_zero (hG : IsLevel G n) (eR : Fin N → ℝ) (ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hψ' : IsLayerConstant G ψ') :
    lineBg hG (fun i => (eR i : ℂ)) ψ' hψ' 0 =
      constBg hG ((1 + (0 : ℂ)) • fun i => (eR i : ℂ)) (fun i => (eR i : ℂ)) := by
  refine BgData.ext' ?_ ?_
  · funext x i; simp [lineBg, constBg]
  · rfl

/-- A uniform bound of the (finitely many) vectors `ψ' x`. -/
theorem exists_bound_layer (ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, vn (ψ' x) ≤ C) ∧ ∀ x x', vn (fun i => ψ' x i - ψ' x' i) ≤ C := by
  classical
  refine ⟨2 * ∑ x, vn (ψ' x), mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => vn_nonneg _),
    fun x => ?_, fun x x' => ?_⟩
  · have := Finset.single_le_sum (f := fun x => vn (ψ' x)) (fun y _ => vn_nonneg _) (Finset.mem_univ x)
    have h0 : 0 ≤ ∑ x, vn (ψ' x) := Finset.sum_nonneg fun y _ => vn_nonneg _
    linarith
  · have h1 := Finset.single_le_sum (f := fun x => vn (ψ' x)) (fun y _ => vn_nonneg _) (Finset.mem_univ x)
    have h2 := Finset.single_le_sum (f := fun x => vn (ψ' x)) (fun y _ => vn_nonneg _) (Finset.mem_univ x')
    have h3 : vn (fun i => ψ' x i - ψ' x' i) ≤ vn (ψ' x) + vn (ψ' x') := by
      have := vn_add' (ψ' x) (fun i => -ψ' x' i)
      have h4 : vn (fun i => -ψ' x' i) = vn (ψ' x') := by
        have := vn_smul_complex (-1) (ψ' x')
        simpa using this
      simp only [← sub_eq_add_neg] at this
      linarith
    linarith

/-- **The line of data lies in the complex union domain for small `|s|`.** -/
theorem inUnionDomainC_line {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν) (hG : IsLevel G n)
    (eR : Fin N → ℝ) (heR : ∑ i, eR i ^ 2 = 1) (ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hψ' : IsLayerConstant G ψ') (hperp : ∀ x, ∑ i, (eR i : ℂ) * ψ' x i = 0) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℂ, ‖s‖ ≤ s₀ →
      InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (lineBg hG (fun i => (eR i : ℂ)) ψ' hψ' s) := by
  classical
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨C, hC0, hCx, hCd⟩ := exists_bound_layer ψ'
  have hc1 : 0 < bgC1 d L N := by
    have h0 := bgC0_pos d L N hd0
    have hK := bgK1_pos d L N
    have hC := lemma53Const_pos d L
    have ha : 0 < approxDelta d L := approxDelta_pos d L
    have hδs := deltaStar_pos d L N hd0
    unfold bgC1; positivity
  set δ : ℝ := min 1 (bgC1 d L N) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos hc1
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδc : δ ≤ bgC1 d L N := min_le_right _ _
  refine ⟨δ / (2 * (C + 1)), by positivity, fun s hs => ?_⟩
  have hsC : ‖s‖ * C ≤ δ / 2 := by
    have : ‖s‖ * (2 * (C + 1)) ≤ δ := by
      calc ‖s‖ * (2 * (C + 1)) ≤ δ / (2 * (C + 1)) * (2 * (C + 1)) :=
            mul_le_mul_of_nonneg_right hs (by positivity)
        _ = δ := by field_simp
    nlinarith [norm_nonneg s]
  have hνε : ν * ((L : ℝ) ^ k) ^ 2 * δ ^ 2 ≤ δ ^ 2 := mul_le_of_le_one_left (sq_nonneg _) H.massLe
  have hδ0c : δ ≤ bgC0 d L N := hδc.trans (bgC1_le_bgC0 d L N hd0)
  refine ⟨δ, δ, hδ0, le_rfl, hδ0c, hδc, hνε, fun _ i => eR i, eR, fun x i => s * ψ' x i,
    fun _ _ => 0, ?_, fun x _ i => ?_, fun x _ i => ?_⟩
  · have hP := (inPsiTildeC_constBg (G := G) eR heR (ν := ν) hδ0 hδ1 0 (by simp; positivity))
    refine
      { hP.toInPsiTilde with
        eps_pos := hδ0
        layerConst' := fun m hm1 hmk x hx x' hx' => by
          funext i; simp only [hψ' m hm1 hmk x hx x' hx']
        hLayerConst' := fun _ _ _ _ _ _ _ => rfl
        c1 := fun x x' _ => ?_
        c2a := fun x _ => ?_
        c2b := fun x _ => ?_
        c3a := fun x _ => ?_
        c3b := fun x _ => ?_ }
    · have e : (fun i => s * ψ' x i) - (fun i => s * ψ' x' i) =
          fun i => s * (ψ' x i - ψ' x' i) := by funext i; simp; ring
      rw [e, vn_smul_complex]
      have := hCd x x'
      nlinarith [norm_nonneg s]
    · rw [show (fun i => s * ψ' x i) = fun i => s * ψ' x i from rfl, vn_smul_complex]
      have := hCx x
      nlinarith [norm_nonneg s]
    · have e : ∑ i, ((eR i : ℂ) + s * ψ' x i) * ((eR i : ℂ) + s * ψ' x i) -
          ∑ i, (eR i : ℂ) * (eR i : ℂ) = s ^ 2 * ∑ i, ψ' x i * ψ' x i := by
        have hp := hperp x
        calc _ = ∑ i, (2 * s * ((eR i : ℂ) * ψ' x i) + s ^ 2 * (ψ' x i * ψ' x i)) := by
              rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
          _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp]; ring
      rw [e, norm_mul, norm_pow]
      have h1 : ‖∑ i, ψ' x i * ψ' x i‖ ≤ vn (ψ' x) ^ 2 := by
        rw [vn_sq]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, sq]
      have h2 := hCx x
      have h3 : vn (ψ' x) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (vn_nonneg _) h2 2
      have h4 : ‖s‖ ^ 2 * C ^ 2 ≤ (δ / 2) ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hsC 2
      have h5 : ‖s‖ ^ 2 * ‖∑ i, ψ' x i * ψ' x i‖ ≤ (δ / 2) ^ 2 :=
        (mul_le_mul_of_nonneg_left (h1.trans h3) (by positivity)).trans h4
      nlinarith
    · have h0 : vn ((fun (_ : Torus d (N₀ * L ^ k)) (_ : Fin N) => (0 : ℂ)) x) = 0 := vn_zero
      rw [h0, mul_zero]; positivity
    · simp only [mul_zero, Finset.sum_const_zero, norm_zero]; positivity
  · simp [lineBg]
  · simp [lineBg]

end Balaban.Fluctuation
