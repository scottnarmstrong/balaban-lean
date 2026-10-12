/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ExpansionDomain
public import Balaban.Background.Theorem73
public import Balaban.SmallField.XiPerturb
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma 2.5, the data domain of `ψ = ψ^{(k)} + ψ'` (FLUCTUATION.md §2.5)

* `composeData_inDomainR`: `θ ∈ Ψ̃(𝔹'; δ)` implies `ψ^{(k)} ∈ Ψ̃(𝔹; C₄ K₁ δ)` (`theorem73_real`, with
  the parameter kept);
* `inPsiTilde_perturb`: a real perturbation `|Ψ₀ - Ψ_B| ≤ ε` of a datum of `Ψ̃(δ_b)` lies in
  `Ψ̃(δ_b + 3 √ε)`;
* `disc_inUnionDomainC`: the disc `{B + τ E : |τ| < R}` of Lemma 2.3 (d) lies in `𝒟` once
  `δ_b + 5 R t ≤ c₁`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a₁ ν : ℝ}

/-- The real data domain of the composed datum: with `D'` in `Ψ̃(𝔹'_k; δ)`, the composed datum is in
`Ψ̃(𝔹_j; C₄ K₁ δ)` (the content of `theorem73_real`, with the parameter kept). -/
theorem composeData_inDomainR (ha₁ : 0 < a₁) (H : BgHyp d L k ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) ν) (h : Precedes G G') {D' : BgData G' N} {δ : ℝ}
    (hδ0 : 0 < δ) (hδc : δ ≤ thm73C1 d L N) (hD : InDomainR G' ν δ D') :
    InDomainR G ν (compC4 d * (bgK1 d L N * δ))
      (composeData h (compWeight L a₁) (bgField G' (compWeight L a₁) ν D') D') := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hL2 : 2 ≤ L := by have := H.hL; omega
  have ha : ∀ j, 1 ≤ j → j ≤ k → compWeight L a₁ j ≠ 0 := fun j hj _ =>
    (compWeight_pos hL2 ha₁ hj).ne'
  obtain ⟨hδ1, h2, hx4, hKds, hsm⟩ := thm73_small (L := L) (N := N) hd0 hδ0 hδc
  have hK1 := bgK1_ge_one d L N
  have hDU : InUnionDomainR G' (bgC1 d L N) ν D' := ⟨δ, hδ0, hδ1, hD⟩
  obtain ⟨φ, α, hs, hb, hu, hunit, -, -⟩ := bg_real H' hδ0 hδ1 hD
  obtain ⟨hfC, hmC⟩ := bgFieldC_eq hs hu
  obtain ⟨hfR, hmR⟩ := theorem72_real H' hDU
  have hf : bgField G' (compWeight L a₁) ν D' = φ := by rw [← hfR, hfC]
  rw [hf]
  have hφre : ∀ z i, (φ (z, i)).im = 0 := fun z i => (hunit z).1 i
  obtain ⟨Ψ0, h0, hP, hΨ0, hh0⟩ := hD
  have hFB : FieldBounds G' (bgK1 d L N * δ) D'.Ψ φ :=
    fieldBounds_of_bgBounds (fun _ _ _ => rfl) hb hs.1.2
  have hmass := mass_bound_spacing H' hδ0 hδ1 hP hΨ0 hh0 hs
  obtain ⟨hdom, hreal⟩ := lemma62 hL2 h ha₁ hK1 hδ0 (by nlinarith) H'.mass H'.massLe D'
    ⟨Ψ0, h0, hP, hΨ0, hh0⟩ φ hφre hFB (fun z => hmass z)
  exact hdom


theorem rn_sub_comm (x y : Fin N → ℝ) : rn (fun i => x i - y i) = rn (fun i => y i - x i) := by
  have := rn_smul (-1) (fun i => x i - y i)
  rw [show (fun i => -1 * (x i - y i)) = fun i => y i - x i by funext i; ring] at this
  simpa using this.symm

theorem abs_dot_le_rn (f g : Fin N → ℝ) : |∑ i, f i * g i| ≤ rn f * rn g := by
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg (rn_nonneg f) (rn_nonneg g))
  rw [mul_pow, rn_sq_sum, rn_sq_sum]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem abs_rn_sub_le (x y : Fin N → ℝ) : |rn x - rn y| ≤ rn (fun i => x i - y i) := by
  have h1 := rn_triangle x y (fun _ => 0)
  have h2 := rn_triangle y x (fun _ => 0)
  have h3 := rn_sub_comm y x
  simp only [sub_zero] at h1 h2
  rw [abs_le]; constructor <;> linarith

theorem r2_perturb {a b ε δb : ℝ} (ha : |a ^ 2 - 1| < δb) (hδb : δb ≤ 1 / 8) (hab : |b - a| ≤ ε)
    (hε : ε ≤ 1 / 8) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) : |b ^ 2 - 1| < δb + 3 * ε := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hab
  have h1 : a ^ 2 < 9 / 8 := by
    have := (abs_lt.1 ha).2; linarith
  have h2 : a ≤ 11 / 10 := by nlinarith
  have h3 : |b ^ 2 - a ^ 2| ≤ 3 * ε := by
    have e : b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring
    rw [e, abs_mul]
    have : |b + a| ≤ 3 := by
      rw [abs_of_nonneg (by linarith)]
      have := (abs_le.1 hab).2
      linarith
    calc |b - a| * |b + a| ≤ ε * 3 := mul_le_mul hab this (abs_nonneg _) hε0
      _ = 3 * ε := by ring
  calc |b ^ 2 - 1| = |(a ^ 2 - 1) + (b ^ 2 - a ^ 2)| := by ring_nf
    _ ≤ |a ^ 2 - 1| + |b ^ 2 - a ^ 2| := abs_add_le _ _
    _ < δb + 3 * ε := by linarith


theorem r3_perturb {u w h : Fin N → ℝ} {c ε δb : ℝ} (hc0 : 0 ≤ c) (hcρ : c * rn h ≤ 2)
    (ha : 9 / 10 ≤ rn u) (hb : 0 < rn w) (hε : rn (fun i => u i - w i) ≤ ε)
    (hr3 : c * |1 - (∑ i, u i * h i) / rn u| < δb ^ 2) :
    c * |1 - (∑ i, w i * h i) / rn w| < δb ^ 2 + 5 * ε := by
  have ha0 : 0 < rn u := by linarith
  have hε0 : 0 ≤ ε := (rn_nonneg _).trans hε
  have e : (∑ i, u i * h i) / rn u - (∑ i, w i * h i) / rn w =
      ∑ i, h i * (u i / rn u - w i / rn w) := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h1 : |(∑ i, u i * h i) / rn u - (∑ i, w i * h i) / rn w| ≤
      rn h * (2 * ε / rn u) := by
    rw [e]
    refine (abs_dot_le_rn _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (rn_nonneg _)
    refine (rn_normalize_sub u w ha0 hb).trans ?_
    exact div_le_div_of_nonneg_right (by linarith) ha0.le
  have h2 : 1 - (∑ i, w i * h i) / rn w =
      (1 - (∑ i, u i * h i) / rn u) + ((∑ i, u i * h i) / rn u - (∑ i, w i * h i) / rn w) := by
    ring
  have h3 : rn h * (2 * ε / rn u) ≤ rn h * (2 * ε / (9 / 10)) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by linarith) (by norm_num) ha)
      (rn_nonneg _)
  calc c * |1 - (∑ i, w i * h i) / rn w|
      ≤ c * (|1 - (∑ i, u i * h i) / rn u| + rn h * (2 * ε / (9 / 10))) := by
        rw [h2]
        refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) hc0
        linarith
    _ = c * |1 - (∑ i, u i * h i) / rn u| + (c * rn h) * (2 * ε / (9 / 10)) := by ring
    _ < δb ^ 2 + 5 * ε := by
        have : (c * rn h) * (2 * ε / (9 / 10)) ≤ 2 * (2 * ε / (9 / 10)) :=
          mul_le_mul_of_nonneg_right hcρ (by positivity)
        linarith


/-- **Stability of the real data domain under a small real perturbation of the data**: if
`(Ψ_B, h) ∈ Ψ̃(δ_b)` and `|Ψ₀ - Ψ_B| ≤ ε` on `Ω₁ ∪ C(Ω₁)` (`δ_b, ε ≤ 1/8`, `ν L^{2k} ≤ 1`,
layers `≤ k`), then `(Ψ₀, h) ∈ Ψ̃(δ_b + 3 √ε)` for a layer-constant `Ψ₀`. -/
theorem inPsiTilde_perturb {ν δb ε : ℝ} {ΨB Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h : Fin N → ℝ} (H : InPsiTilde G ν δb ΨB h) (hconst : IsLayerConstant G Ψ₀)
    (hδb0 : 0 ≤ δb) (hδb : δb ≤ 1 / 8) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8) (hν0 : 0 ≤ ν)
    (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) (hlay : ∀ x ∈ dataSites G, G.layerIndex x ≤ k)
    (he : ∀ x ∈ dataSites G, rn (fun i => Ψ₀ x i - ΨB x i) ≤ ε) :
    InPsiTilde G ν (δb + 3 * Real.sqrt ε) Ψ₀ h := by
  have hsε : ε ≤ Real.sqrt ε := by
    calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε0).symm
      _ ≤ Real.sqrt ε := Real.sqrt_le_sqrt (by nlinarith)
  have hs0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  refine ⟨hconst, ?_, ?_, ?_, ?_⟩
  · intro x x' hxx'
    have h1 := H.r1 x x' hxx'
    have e1 := he x hxx'.1
    have e2 := he x' hxx'.2.1
    have t1 := rn_triangle (fun i => Ψ₀ x i) (fun i => ΨB x i) (fun i => Ψ₀ x' i)
    have t2 := rn_triangle (fun i => ΨB x i) (fun i => ΨB x' i) (fun i => Ψ₀ x' i)
    have t3 := rn_sub_comm (fun i => ΨB x' i) (fun i => Ψ₀ x' i)
    linarith
  · intro x hx
    have h1 := H.r2 x hx
    have a0 := rn_nonneg (ΨB x)
    have b0 := rn_nonneg (Ψ₀ x)
    have hA : |rn (ΨB x) ^ 2 - 1| < δb := by rw [rn_sq_sum]; exact h1
    have hab : |rn (Ψ₀ x) - rn (ΨB x)| ≤ ε := (abs_rn_sub_le _ _).trans (he x hx)
    have := r2_perturb hA hδb hab hε a0 b0
    rw [rn_sq_sum] at this
    linarith
  · intro x hx
    have h1 := H.r3 x hx
    set c := ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 with hc
    have hc0 : 0 ≤ c := by positivity
    have hcC : c ≤ ν * ((L : ℝ) ^ k) ^ 2 := by
      rw [hc]
      refine mul_le_mul_of_nonneg_left ?_ hν0
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 (hlay x hx)) 2
    have hc1 : c ≤ 1 := hcC.trans hν1
    have hr4 := H.r4
    have hrh : c * rn h ^ 2 ≤ 2 := by
      rw [rn_sq_sum]
      have hS : ν * ((L : ℝ) ^ k) ^ 2 * ∑ i, h i ^ 2 ≤ 2 := by
        have : ν * ((L : ℝ) ^ k) ^ 2 * ∑ i, h i ^ 2 ≤
            ν * ((L : ℝ) ^ k) ^ 2 + ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, h i ^ 2 - 1| := by
          have h2 : ∑ i, h i ^ 2 ≤ 1 + |∑ i, h i ^ 2 - 1| := by
            have := le_abs_self (∑ i, h i ^ 2 - 1); linarith
          nlinarith [mul_nonneg hν0 (sq_nonneg ((L : ℝ) ^ k))]
        nlinarith
      have hsq : 0 ≤ ∑ i, h i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hcC hsq]
    have hcρ : c * rn h ≤ 2 := by
      have h0 := rn_nonneg h
      nlinarith [sq_nonneg (c * rn h), mul_nonneg hc0 h0]
    have hA : |rn (ΨB x) ^ 2 - 1| < δb := by
      rw [rn_sq_sum]; exact H.r2 x hx
    have ha : 9 / 10 ≤ rn (ΨB x) := by
      have h7 : 7 / 8 < rn (ΨB x) ^ 2 := by have := (abs_lt.1 hA).1; linarith
      by_contra hcon
      push Not at hcon
      have := rn_nonneg (ΨB x)
      nlinarith
    have hd := he x hx
    have hbpos : 0 < rn (Ψ₀ x) := by
      have := abs_rn_sub_le (ΨB x) (Ψ₀ x)
      have h3 := rn_sub_comm (fun i => Ψ₀ x i) (fun i => ΨB x i)
      have := (abs_le.1 this).2
      linarith
    have hd' : rn (fun i => ΨB x i - Ψ₀ x i) ≤ ε := by rw [rn_sub_comm]; exact hd
    have := r3_perturb hc0 hcρ ha hbpos hd' h1
    calc _ < δb ^ 2 + 5 * ε := this
      _ ≤ (δb + 3 * Real.sqrt ε) ^ 2 := by
          have : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε0
          nlinarith [mul_nonneg hδb0 hs0]
  · have := H.r4
    refine this.trans_le (pow_le_pow_left₀ hδb0 (by linarith) 2)


/-- **The disc of Lemma 2.3 (d) lies in the data domain**: the line `B + τ E`, `|τ| < R`, of a real
datum `B ∈ Ψ̃(δ_b)` and a tangent `E` (with `h̃ = 0`, `|E| ≤ t`) lies in `𝒟(c₀, c₁)` once
`δ_b + 5 R t ≤ c₁` (and `δ_b ≤ 1/4`, `R t ≤ 1`). -/
theorem disc_inUnionDomainC (hd : 0 < d) {ν δb t R : ℝ} {B E : BgData G N}
    (hB : InDomainR G ν δb B) (hδb0 : 0 < δb) (hδb : δb ≤ 1 / 4) (ht0 : 0 ≤ t) (hR0 : 0 ≤ R)
    (hRt : R * t ≤ 1) (hEh : ∀ x i, E.h x i = 0)
    (hE : ∀ x ∈ dataSites G, vn (E.Ψ x) ≤ t) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hc1 : δb + 5 * (R * t) ≤ bgC1 d L N) {τ : ℂ} (hτ : ‖τ‖ < R) :
    InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (B.lineAt E τ) := by
  obtain ⟨ΨB, h, hP, hΨ, hh⟩ := hB
  have hP0 : InPsiTildeC G ν δb δb ΨB h (fun _ _ => 0) (fun _ _ => 0) :=
    (DataWit.ofReal (ν := ν) hδb0 hδb0 hP B hΨ hh).P
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
  have hP2 := SmallField.perturb_inPsiTildeC (ν := ν) (by linarith) hδ₃ hRt hP0 hlc hbd
  have hδ' : 0 < δb + 5 * (R * t) := by linarith
  refine ⟨δb + 5 * (R * t), δb + 5 * (R * t), hδ', le_rfl,
    hc1.trans (bgC1_le_bgC0 d L N hd), hc1, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hν1 (sq_nonneg (δb + 5 * (R * t)))
    nlinarith [sq_nonneg (δb + 5 * (R * t))]
  · refine ⟨ΨB, h, fun x i => (0 : ℂ) + τ * E.Ψ x i, fun _ _ => 0, ?_, ?_, ?_⟩
    · simpa using hP2
    · intro x hx i
      simp only [BgData.lineAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hΨ x hx i]
      ring
    · intro x hx i
      simp only [BgData.lineAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hEh]
      rw [hh x hx i]
      ring

end Balaban.Fluctuation
