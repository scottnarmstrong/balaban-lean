/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Lemma25Domain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The disc of Lemma 2.3 (d) around a complex datum (W136b)

`disc_inUnionDomainC` (Lemma25Domain) treats the disc `{B + τ E : |τ| < R}` around a *real* datum.
The composed datum `ψ^{(k)}` of a member of `Ξ^c` is complex, in `Ψ̃^c(δ, ε)` with `δ ≤ ε`.  Here:

* `perturb_inPsiTildeC_gen`: the perturbation estimate of `perturb_inPsiTildeC` for `δ ≤ ε`
  (output `Ψ̃^c(δ + 5 δ₃, max ε (δ + 5 δ₃))`);
* `disc_inUnionDomainC_gen`: the disc around a datum of `Ψ̃^c(δ, ε)` lies in `𝒟(c₀, c₁)` once
  `δ + 5 R t ≤ c₁`;
* `composeData_inDomainC_explicit`: `theorem73_complex_witness` with the parameters kept explicit,
  `δ₀ = 2 C₄ K₁ δ`, `ε₀ = max ε δ₀`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Matrix

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a₁ ν : ℝ}

section Perturb

variable {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- **The perturbed data domain for `δ ≤ ε`**: if `(Ψ₀ + Ψ'', h₀ + h'') ∈ Ψ̃^c(δ, ε)` and
`|δΨ| ≤ δ₃` then `(Ψ₀ + Ψ'' + δΨ, h₀ + h'') ∈ Ψ̃^c(δ + 5 δ₃, max ε (δ + 5 δ₃))`. -/
theorem perturb_inPsiTildeC_gen {δ ε δ₃ : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hδ : δ ≤ 1 / 4)
    (hε : ε ≤ 1 / 4) (hδ₃ : 0 ≤ δ₃) (hδ₃1 : δ₃ ≤ 1)
    (hP : InPsiTildeC G ν δ ε Ψ₀ h₀ Ψ'' h'') {δΨ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hδΨc : IsLayerConstant G δΨ) (hδΨ : ∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₃) :
    InPsiTildeC G ν (δ + 5 * δ₃) (max ε (δ + 5 * δ₃)) Ψ₀ h₀ (fun x i => Ψ'' x i + δΨ x i) h'' := by
  have hle : δ ≤ δ + 5 * δ₃ := by linarith
  have hε0 : 0 < ε := lt_of_lt_of_le hδ0 hδε
  refine ⟨hP.toInPsiTilde.mono hδ0.le hle, lt_of_lt_of_le hε0 (le_max_left _ _), ?_,
    hP.hLayerConst', ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn1 hnk x hx x' hx'
    funext i
    show Ψ'' x' i + δΨ x' i = Ψ'' x i + δΨ x i
    rw [congrFun (hP.layerConst' n hn1 hnk x hx x' hx') i,
      congrFun (hδΨc n hn1 hnk x hx x' hx') i]
  · intro x x' hxx'
    have h1 := hP.c1 x x' hxx'
    have h2 := hδΨ x hxx'.1
    have h3 := hδΨ x' hxx'.2.1
    have e : (fun i => Ψ'' x i + δΨ x i) - (fun i => Ψ'' x' i + δΨ x' i) =
        (fun i => (Ψ'' x - Ψ'' x') i + (δΨ x - δΨ x') i) := by
      funext i; simp only [Pi.sub_apply]; ring
    show vn ((fun i => Ψ'' x i + δΨ x i) - (fun i => Ψ'' x' i + δΨ x' i)) < _
    rw [e]
    have t := vn_add' (Ψ'' x - Ψ'' x') (δΨ x - δΨ x')
    have t2 := vn_sub_le_add (δΨ x) (δΨ x')
    linarith
  · intro x hx
    have h1 := hP.c2a x hx
    have h2 := hδΨ x hx
    have t := vn_add' (Ψ'' x) (δΨ x)
    have : ε ≤ max ε (δ + 5 * δ₃) := le_max_left _ _
    linarith
  · intro x hx
    have hold := hP.c2b x hx
    have hr2 := hP.r2 x hx
    have hrn : rn (Ψ₀ x) ≤ 3 / 2 := by
      have hsq : rn (Ψ₀ x) ^ 2 ≤ 5 / 4 := by
        rw [rn_sq_sum]; have := (abs_lt.1 hr2).2; linarith
      nlinarith [rn_nonneg (Ψ₀ x)]
    have hΨ'' := hP.c2a x hx
    have hw : vn (fun i => (Ψ₀ x i : ℂ) + Ψ'' x i) ≤ 2 := by
      have e : vn (fun i => (Ψ₀ x i : ℂ)) = rn (Ψ₀ x) := vn_ofReal _
      have := vn_add' (fun i => (Ψ₀ x i : ℂ)) (Ψ'' x)
      linarith
    have h2 := hδΨ x hx
    have key : ∀ i, ((Ψ₀ x i : ℂ) + (Ψ'' x i + δΨ x i)) * ((Ψ₀ x i : ℂ) + (Ψ'' x i + δΨ x i)) -
        (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ) =
        (((Ψ₀ x i : ℂ) + Ψ'' x i) * ((Ψ₀ x i : ℂ) + Ψ'' x i) - (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ)) +
        (2 * (((Ψ₀ x i : ℂ) + Ψ'' x i) * δΨ x i) + δΨ x i * δΨ x i) := fun i => by ring
    have e : ∑ i, ((Ψ₀ x i : ℂ) + (Ψ'' x i + δΨ x i)) * ((Ψ₀ x i : ℂ) + (Ψ'' x i + δΨ x i)) -
        ∑ i, (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ) =
        (∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * ((Ψ₀ x i : ℂ) + Ψ'' x i) -
          ∑ i, (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ)) +
        (2 * ∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * δΨ x i + ∑ i, δΨ x i * δΨ x i) := by
      rw [← Finset.sum_sub_distrib]
      simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
    show ‖∑ i, ((Ψ₀ x i : ℂ) + (Ψ'' x i + δΨ x i)) * ((Ψ₀ x i : ℂ) + (Ψ'' x i + δΨ x i)) -
      ∑ i, (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ)‖ < _
    rw [e]
    have t1 : ‖∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * δΨ x i‖ ≤ 2 * δ₃ :=
      (norm_dot_le _ _).trans (mul_le_mul hw h2 (vn_nonneg _) (by norm_num))
    have t2 : ‖∑ i, δΨ x i * δΨ x i‖ ≤ δ₃ * δ₃ :=
      (norm_dot_le _ _).trans (mul_le_mul h2 h2 (vn_nonneg _) hδ₃)
    have n2 : ‖(2 : ℂ)‖ = 2 := by simp
    have hB : ‖2 * ∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * δΨ x i + ∑ i, δΨ x i * δΨ x i‖ ≤
        2 * (2 * δ₃) + δ₃ * δ₃ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ t2)
      rw [norm_mul, n2]
      exact mul_le_mul_of_nonneg_left t1 (by norm_num)
    have hA := norm_add_le (∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * ((Ψ₀ x i : ℂ) + Ψ'' x i) -
      ∑ i, (Ψ₀ x i : ℂ) * (Ψ₀ x i : ℂ)) (2 * ∑ i, ((Ψ₀ x i : ℂ) + Ψ'' x i) * δΨ x i +
        ∑ i, δΨ x i * δΨ x i)
    nlinarith
  · intro x hx
    have h := hP.c3a x hx
    have hδ' : 0 < δ + 5 * δ₃ := by linarith
    have hstep : δ ^ 2 / ε ≤ (δ + 5 * δ₃) ^ 2 / max ε (δ + 5 * δ₃) := by
      rcases le_total ε (δ + 5 * δ₃) with he | he
      · rw [max_eq_right he]
        have e2 : (δ + 5 * δ₃) ^ 2 / (δ + 5 * δ₃) = δ + 5 * δ₃ := by field_simp
        rw [e2, div_le_iff₀ hε0]
        nlinarith
      · rw [max_eq_left he]
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hδ0.le hle 2) hε0.le
    exact h.trans_le hstep
  · intro x hx
    have h := hP.c3b x hx
    exact h.trans_le (pow_le_pow_left₀ hδ0.le hle 2)

end Perturb

section Disc

/-- **The disc of Lemma 2.3 (d) around a complex datum**: the line `B + τ E`, `|τ| < R`, of a datum
`B ∈ Ψ̃^c(δ, ε)` (`δ ≤ ε ≤ min (c₀, 1/4)`, `ν L^{2k} ε² ≤ δ²`) and a tangent `E` (with `h̃ = 0`,
`|E| ≤ t` on the data sites) lies in `𝒟(c₀, c₁)` once `δ + 5 R t ≤ c₁` (and `R t ≤ 1`). -/
theorem disc_inUnionDomainC_gen (hd : 0 < d) {ν δ ε t R : ℝ} {B E : BgData G N}
    (hB : InDomainC G ν δ ε B) (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hδ : δ ≤ 1 / 4) (hε : ε ≤ 1 / 4)
    (hεc : ε ≤ bgC0 d L N) (hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (ht0 : 0 ≤ t) (hR0 : 0 ≤ R) (hRt : R * t ≤ 1) (hEh : ∀ x i, E.h x i = 0)
    (hE : ∀ x ∈ dataSites G, vn (E.Ψ x) ≤ t) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hc1 : δ + 5 * (R * t) ≤ bgC1 d L N) {τ : ℂ} (hτ : ‖τ‖ < R) :
    InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (B.lineAt E τ) := by
  obtain ⟨ΨB, h, Ψ'', h'', hP0, hΨ, hh⟩ := hB
  have hδ₃ : 0 ≤ R * t := mul_nonneg hR0 ht0
  have hlc : IsLayerConstant G (fun x i => τ * E.Ψ x i) := by
    intro n hn1 hnk x hx x' hx'
    funext i
    simp only [E.Ψ_layerConst n hn1 hnk x hx x' hx']
  have hbd : ∀ x ∈ dataSites G, vn (fun i => τ * E.Ψ x i) ≤ R * t := by
    intro x hx
    rw [vn_smul_complex]
    have := hE x hx
    exact mul_le_mul hτ.le this (vn_nonneg _) hR0
  have hP2 := perturb_inPsiTildeC_gen hδ0 hδε hδ hε hδ₃ hRt hP0 hlc hbd
  have hδ' : 0 < δ + 5 * (R * t) := by linarith
  have hc0 : δ + 5 * (R * t) ≤ bgC0 d L N := hc1.trans (bgC1_le_bgC0 d L N hd)
  refine ⟨δ + 5 * (R * t), max ε (δ + 5 * (R * t)), hδ', le_max_right _ _, max_le hεc hc0, hc1,
    ?_, ?_⟩
  · rcases le_total ε (δ + 5 * (R * t)) with he | he
    · rw [max_eq_right he]
      have := mul_le_mul_of_nonneg_right hν1 (sq_nonneg (δ + 5 * (R * t)))
      nlinarith [sq_nonneg (δ + 5 * (R * t))]
    · rw [max_eq_left he]
      have : δ ^ 2 ≤ (δ + 5 * (R * t)) ^ 2 := pow_le_pow_left₀ hδ0.le (by linarith) 2
      linarith
  · refine ⟨ΨB, h, fun x i => Ψ'' x i + τ * E.Ψ x i, h'', hP2, ?_, ?_⟩
    · intro x hx i
      simp only [BgData.lineAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hΨ x hx i]
      ring
    · intro x hx i
      simp only [BgData.lineAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hEh]
      rw [hh x hx i]
      ring

end Disc

section Explicit

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- **Theorem 7.3 (complex data) with the parameters explicit**: for `D' ∈ Ψ̃^c(𝔹'; δ, ε)` with
`δ ≤ thm73C3`, `ε ≤ c₀`, the composed datum lies in `Ψ̃^c(𝔹; δ₀, max ε δ₀)`, `δ₀ = 2 C₄ K₁ δ`
(`theorem73_complex_witness`, whose conclusion hides `δ₀`). -/
theorem composeData_inDomainC_explicit (ha₁ : 0 < a₁) (H : BgHyp d L k ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) ν) (h : Precedes G G') {D' : BgData G' N} {δ ε : ℝ}
    (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδc : δ ≤ thm73C3 d L N)
    (hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hDC : InDomainC G' ν δ ε D') :
    0 < 2 * (compC4 d * (bgK1 d L N * δ)) ∧ δ ≤ 2 * (compC4 d * (bgK1 d L N * δ)) ∧
      2 * (compC4 d * (bgK1 d L N * δ)) ≤ bgC0 d L N ∧
      2 * (compC4 d * (bgK1 d L N * δ)) ≤ bgC2 d L N ∧
      ν * ((L : ℝ) ^ k) ^ 2 * (max ε (2 * (compC4 d * (bgK1 d L N * δ)))) ^ 2 ≤
        (2 * (compC4 d * (bgK1 d L N * δ))) ^ 2 ∧
      InDomainC G ν (2 * (compC4 d * (bgK1 d L N * δ)))
        (max ε (2 * (compC4 d * (bgK1 d L N * δ))))
        (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D') := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hL2 : 2 ≤ L := by have := H.hL; omega
  have ha : ∀ j, 1 ≤ j → j ≤ k → compWeight L a₁ j ≠ 0 := fun j hj _ =>
    (compWeight_pos hL2 ha₁ hj).ne'
  have hδc2 : δ ≤ thm73C2 d L N := hδc.trans (thm73C3_le_thm73C2 d L N)
  have hδc1 : δ ≤ thm73C1 d L N := hδc2.trans (thm73C2_le_thm73C1 d L N)
  have h2s : 2 * (compC4 d * (bgK1 d L N * δ)) ≤ bgC2 d L N := by
    have hpos : 0 < 2 * (compC4 d * bgK1 d L N) := by
      have := compC4_ge d; have := bgK1_ge_one d L N; positivity
    have := (le_div_iff₀ hpos).1 hδc2
    nlinarith
  obtain ⟨hδ1, h2, hx4, hKds, hsm⟩ := thm73_small (L := L) (N := N) hd0 hδ0 hδc1
  have hK1 := bgK1_ge_one d L N
  obtain ⟨W⟩ := DataWit.exists hDC
  -- the complex small solution and the real one
  obtain ⟨φc, αc, hsc, hbc, huc⟩ := theorem52_exists H' hδ0 hδε hε hδ1 hνε hDC
  obtain ⟨hfc, hmc⟩ := bgFieldC_eq hsc huc
  have hDr : InDomainR G' ν δ W.real :=
    ⟨W.Ψ, W.h₀, W.P.toInPsiTilde, fun x hx i => W.real_Ψ hx i, fun x hx i => W.real_h hx i⟩
  obtain ⟨φr, αr, hsr, hbr, hur, hunitr, -, -⟩ := bg_real H' hδ0 hδ1 hDr
  have hφr : ∀ z i, (φr (z, i)).im = 0 := fun z i => (hunitr z).1 i
  have hdiff : ∀ z : G'.Ω 1, vn (fun i => φc (z, i) - φr (z, i)) ≤ ε + bgK1 d L N * δ := fun z =>
    theorem52_compare H' hδ0 hδε hε hδ1 hνε W W.real (fun x hx i => W.real_Ψ hx i)
      (fun x hx i => W.real_h hx i) hsc hsr z
  have hmass : ∀ z : G'.Ω 1,
      Real.sqrt ν * G'.spacing z * vn (fun i => φr (z, i) - (W.h₀ i : ℂ)) ≤ bgK1 d L N * δ := by
    intro z
    have := mass_bound_spacing H' hδ0 hδ1 W.P.toInPsiTilde (fun x hx i => W.real_Ψ hx i)
      (fun x hx i => W.real_h hx i) hsr z
    have e : (fun i => φr (z, i) - W.real.h z i) = fun i => φr (z, i) - (W.h₀ i : ℂ) :=
      funext fun i => by rw [W.real_h z.2 i]
    rwa [e] at this
  have hcons : Hyp63 G G' a₁ ν δ ε (bgK1 d L N) (bgK1 d L N * δ) W.Ψ W.h₀ W.Ψ' W.h' φr φc :=
    { prec := h, hL := hL2, ha₁ := ha₁, hK₁ := hK1, hδ := hδ0, hδε := hδε
      hε1 := hε.trans (bgC0_le d L N |>.trans (by norm_num)), hη := rfl
      hsmall := hsm, hν := H'.mass, hνk := H'.massLe, hPC := W.P, hφr := hφr
      hbr := fieldBounds_of_bgBounds (fun x hx i => (W.real_Ψ hx i).symm) hbr hsr.1.2
      hmass := hmass
      hbc := fieldBounds_of_bgBounds (fun x hx i => by rw [W.hΨ x hx i]; rfl) hbc hsc.1.2
      hdiff := hdiff }
  have hdom := lemma63_inDomainC hcons D' (fun x hx i => by rw [W.hΨ x hx i]; rfl)
    (fun x hx i => W.hh x hx i)
  rw [hfc]
  have hδj0 : 0 < 2 * (compC4 d * (bgK1 d L N * δ)) := by
    have := compC4_ge d; positivity
  have hδjc0 : 2 * (compC4 d * (bgK1 d L N * δ)) ≤ bgC0 d L N :=
    h2.trans (bgC1_le_bgC0 d L N hd0)
  have hδδj : δ ≤ 2 * (compC4 d * (bgK1 d L N * δ)) := by
    have := compC4_ge d
    nlinarith [mul_pos hδ0 (by linarith : (0 : ℝ) < bgK1 d L N)]
  have hνj : ν * ((L : ℝ) ^ k) ^ 2 * (max ε (2 * (compC4 d * (bgK1 d L N * δ)))) ^ 2 ≤
      (2 * (compC4 d * (bgK1 d L N * δ))) ^ 2 := by
    rcases le_total ε (2 * (compC4 d * (bgK1 d L N * δ))) with he | he
    · rw [max_eq_right he]
      have := H.massLe
      nlinarith [sq_nonneg (2 * (compC4 d * (bgK1 d L N * δ)))]
    · rw [max_eq_left he]
      have : δ ^ 2 ≤ (2 * (compC4 d * (bgK1 d L N * δ))) ^ 2 :=
        pow_le_pow_left₀ hδ0.le hδδj 2
      linarith
  exact ⟨hδj0, hδδj, hδjc0, h2s, hνj, hdom⟩

end Explicit

end Balaban.Fluctuation
