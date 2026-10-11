/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Theorem52
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 5.2 (4): the bounds P2 (1.16) for real data

For real data `(Ψ, h) ∈ Ψ̃(δ)` and the small solution `φ`:

* `bg_mass_bound`: `√ν |φ - h|(x) ≤ K₁ δ / ℓ(x)`;
* `bg_mass_dot_bound`: `ν |φ(x) · h'(x)| ≤ (K₁ + 2) δ² / ℓ(x)²` for every `h'` satisfying the
  condition (C3) of `Ψ̃^c(δ, ε)` with `δ ≤ ε`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν δ : ℝ} {D : BgData G N}

theorem sqrt_mul_spacing_le (S : ApproxSetting d L k ϱ a ν δ δ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) : Real.sqrt ν * G.spacing x ≤ 1 := by
  obtain ⟨hB0, hB1⟩ := blockMass_le S hx
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hℓ : 0 < G.spacing x := spacing_pos G
  have h1 : Real.sqrt (blockMass G ν x) = Real.sqrt ν * G.spacing x := by
    unfold blockMass GeneratingSet.spacing
    rw [Real.sqrt_mul S.hν0, Real.sqrt_sq (by positivity)]
  rw [← h1]
  calc Real.sqrt (blockMass G ν x) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hB1
    _ = 1 := Real.sqrt_one

/-- **P2 (1.16), first bound**: `√ν |φ - h|(x) ≤ K₁ δ / ℓ(x)` for real data. -/
theorem bg_mass_bound (H : BgHyp d L k ϱ a ν) (hδ0 : 0 < δ) (hδ : δ ≤ bgC1 d L N)
    {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ} (hP : InPsiTilde G ν δ Ψ h₀)
    (hΨ : ∀ x ∈ dataSites G, ∀ i, D.Ψ x i = (Ψ x i : ℂ)) (hh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h₀ i : ℂ))
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hs : IsSmallSolution G a ν (bgC0 d L N) D φ α)
    (x : G.Ω 1) :
    Real.sqrt ν * vn (fun i => φ (x, i) - D.h x i) ≤ bgK1 d L N * δ / G.spacing x.1 := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨hδa, -, -, -⟩ := bgC1_facts d L N hd0 hδ
  have hδc0 : δ ≤ bgC0 d L N := hδ.trans (bgC1_le_bgC0 d L N hd0)
  have hνε : ν * ((L : ℝ) ^ k) ^ 2 * δ ^ 2 ≤ δ ^ 2 := by
    have := H.massLe
    nlinarith [sq_nonneg δ]
  have S : ApproxSetting d L k ϱ a ν δ δ :=
    H.approxSetting hδ0 le_rfl (hδc0.trans (bgC0_le d L N)) (approxDelta_le d L hδa).1 hνε
  let W : DataWit G ν δ δ D := DataWit.ofReal hδ0 hδ0 hP D hΨ hh
  obtain ⟨φ1, α1, -, -, hsup, hu⟩ := bg_core H hδ0 le_rfl hδc0 hδ hνε W
  have e1 := (hu φ α hs).1
  obtain ⟨-, -, -, -, -, -, -, -, -, hmass⟩ := lemma53 S hδa D D W hΨ hh
  have hxd : x.1 ∈ G.Ω 1 := x.2
  have hm := hmass x.1 hxd
  have hℓ : 0 < G.spacing x.1 := spacing_pos G
  have hsq := sqrt_mul_spacing_le S hxd
  have hsq0 := Real.sqrt_nonneg ν
  have hC0 := lemma53Const_pos d L
  have hK2 := cK2_pos d L N
  have hV : 0 ≤ cK2 d L N * (lemma53Const d L * δ) := by positivity
  have hv : vn (fun i => φ (x, i) - approxField G a ν D.Ψ D.h x i) ≤
      N * (cK2 d L N * (lemma53Const d L * δ)) := by
    refine vn_le_card_mul hV fun i => ?_
    have := hsup.val x i
    rw [svec_of_mem G _ x i] at this
    rw [e1]; exact this
  have e : (fun i => φ (x, i) - D.h x i) =
      (approxField G a ν D.Ψ D.h x.1 - cplx h₀) +
        (fun i => φ (x, i) - approxField G a ν D.Ψ D.h x.1 i) := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, cplx, hh x.1 hxd i]
    ring
  rw [e]
  have h1 := vn_add (approxField G a ν D.Ψ D.h x.1 - cplx h₀)
    (fun i => φ (x, i) - approxField G a ν D.Ψ D.h x.1 i)
  have h2 : Real.sqrt ν * vn (fun i => φ (x, i) - approxField G a ν D.Ψ D.h x.1 i) ≤
      N * (cK2 d L N * (lemma53Const d L * δ)) / G.spacing x.1 := by
    rw [le_div_iff₀ hℓ]
    calc Real.sqrt ν * vn (fun i => φ (x, i) - approxField G a ν D.Ψ D.h x.1 i) * G.spacing x.1
        = (Real.sqrt ν * G.spacing x.1) *
          vn (fun i => φ (x, i) - approxField G a ν D.Ψ D.h x.1 i) := by ring
      _ ≤ 1 * (N * (cK2 d L N * (lemma53Const d L * δ))) :=
          mul_le_mul hsq hv (vn_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hK : lemma53Const d L * δ + N * (cK2 d L N * (lemma53Const d L * δ)) ≤ bgK1 d L N * δ := by
    unfold bgK1
    have : 0 ≤ (L + 2 * d * (L : ℝ) ^ 2 + (N + 1) * cK2 d L N) * (lemma53Const d L * δ) := by
      positivity
    nlinarith
  have h3 : Real.sqrt ν * (vn (approxField G a ν D.Ψ D.h x.1 - cplx h₀) +
      vn (fun i => φ (x, i) - approxField G a ν D.Ψ D.h x.1 i)) ≤ bgK1 d L N * δ / G.spacing x.1 := by
    have : Real.sqrt ν * vn (approxField G a ν D.Ψ D.h x.1 - cplx h₀) ≤
        lemma53Const d L * δ / G.spacing x.1 := hm
    have e3 : bgK1 d L N * δ / G.spacing x.1 ≥
        lemma53Const d L * δ / G.spacing x.1 +
          N * (cK2 d L N * (lemma53Const d L * δ)) / G.spacing x.1 := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hK hℓ.le
    nlinarith
  calc Real.sqrt ν * vn ((approxField G a ν D.Ψ D.h x.1 - cplx h₀) +
        (fun i => φ (x, i) - approxField G a ν D.Ψ D.h x.1 i))
      ≤ Real.sqrt ν * (vn (approxField G a ν D.Ψ D.h x.1 - cplx h₀) +
        vn (fun i => φ (x, i) - approxField G a ν D.Ψ D.h x.1 i)) :=
        mul_le_mul_of_nonneg_left h1 hsq0
    _ ≤ _ := h3

/-- The unit vector `Ψ/|Ψ|` is within `δ` of `Ψ` (from (R2)). -/
theorem vn_unit_sub_le {Ψ : Fin N → ℝ} {δ : ℝ} (hδ : δ ≤ 1 / 1024)
    (h2 : |∑ i, Ψ i ^ 2 - 1| < δ) (hδ0 : 0 < δ) :
    0 < rn Ψ ∧ vn (cplx Ψ - fun i => ((Ψ i / rn Ψ : ℝ) : ℂ)) ≤ δ := by
  have hsum : 0 < ∑ i, Ψ i ^ 2 := by
    have := (abs_lt.1 h2).1
    linarith
  have hr : 0 < rn Ψ := Real.sqrt_pos.2 hsum
  refine ⟨hr, ?_⟩
  have e : (cplx Ψ - fun i => ((Ψ i / rn Ψ : ℝ) : ℂ)) = (((1 - (rn Ψ)⁻¹ : ℝ)) : ℂ) • cplx Ψ := by
    funext i
    simp only [Pi.sub_apply, cplx, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  rw [vn_eq_cNorm, e, cNorm_smul, cNorm_cplx_eq_rn, Complex.norm_real, Real.norm_eq_abs]
  have hrsq : rn Ψ ^ 2 = ∑ i, Ψ i ^ 2 := rn_sq Ψ
  have : |1 - (rn Ψ)⁻¹| * rn Ψ = |rn Ψ - 1| := by
    rw [← abs_of_pos hr, ← abs_mul, abs_of_pos hr]
    congr 1
    field_simp
  rw [this]
  have h3 : |rn Ψ - 1| * (rn Ψ + 1) = |rn Ψ ^ 2 - 1| := by
    have e2 : |rn Ψ - 1| * (rn Ψ + 1) = |(rn Ψ - 1) * (rn Ψ + 1)| := by
      rw [abs_mul, abs_of_pos (by linarith : 0 < rn Ψ + 1)]
    rw [e2]; congr 1; ring
  rw [hrsq] at h3
  have : |rn Ψ - 1| ≤ |rn Ψ - 1| * (rn Ψ + 1) := by
    have := abs_nonneg (rn Ψ - 1)
    nlinarith
  linarith

/-- **P2 (1.16), second bound**: for real data in `Ψ̃(δ)` and `h'` satisfying (C3) with `δ ≤ ε`:
`ν |φ(x) · h'(x)| ≤ (K₁ + 2) δ² / ℓ(x)²`. -/
theorem bg_mass_dot_bound (H : BgHyp d L k ϱ a ν) (hδ0 : 0 < δ) (hδ : δ ≤ bgC1 d L N)
    {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ} (hP : InPsiTilde G ν δ Ψ h₀)
    (hΨ : ∀ x ∈ dataSites G, ∀ i, D.Ψ x i = (Ψ x i : ℂ)) (hh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h₀ i : ℂ))
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hs : IsSmallSolution G a ν (bgC0 d L N) D φ α)
    {ε : ℝ} (hε0 : 0 < ε) (hδε : δ ≤ ε) {h' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (c3a : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h' x) < δ ^ 2 / ε)
    (c3b : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
      ‖∑ i, ((Ψ x i / rn (Ψ x) : ℝ) : ℂ) * h' x i‖ < δ ^ 2) (x : G.Ω 1) :
    ν * ‖∑ i, φ (x, i) * h' x.1 i‖ ≤ (bgK1 d L N + 2) * δ ^ 2 / G.spacing x.1 ^ 2 := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨hδa, -, -, -⟩ := bgC1_facts d L N hd0 hδ
  have hδc0 : δ ≤ bgC0 d L N := hδ.trans (bgC1_le_bgC0 d L N hd0)
  have hνε : ν * ((L : ℝ) ^ k) ^ 2 * δ ^ 2 ≤ δ ^ 2 := by
    have := H.massLe
    nlinarith [sq_nonneg δ]
  let W : DataWit G ν δ δ D := DataWit.ofReal hδ0 hδ0 hP D hΨ hh
  obtain ⟨φ1, α1, -, hb, -, hu⟩ := bg_core H hδ0 le_rfl hδc0 hδ hνε W
  have e1 := (hu φ α hs).1
  have hxd : x.1 ∈ dataSites G := (mem_dataSites G).2 (Or.inl x.2)
  have hval : vn (fun i => φ (x, i) - D.Ψ x.1 i) ≤ bgK1 d L N * δ := by
    rw [e1]; exact hb.val x
  have hδ1024 : δ ≤ 1 / 1024 := (approxDelta_le d L hδa).1
  obtain ⟨hr, hunit⟩ := vn_unit_sub_le hδ1024 (hP.r2 x.1 hxd) hδ0
  set u : Fin N → ℂ := fun i => ((Ψ x.1 i / rn (Ψ x.1) : ℝ) : ℂ) with hu_def
  have hℓ : 0 < G.spacing x.1 := spacing_pos G
  have hspx : G.spacing x.1 = (L : ℝ) ^ G.layerIndex x.1 := rfl
  have hΨx : D.Ψ x.1 = cplx (Ψ x.1) := funext fun i => by simp [cplx, hΨ x.1 hxd i]
  have hdiff : vn (fun i => φ (x, i) - u i) ≤ (bgK1 d L N + 1) * δ := by
    have e : (fun i => φ (x, i) - u i) = (fun i => φ (x, i) - D.Ψ x.1 i) +
        (cplx (Ψ x.1) - u) := by
      funext i; simp only [Pi.add_apply, Pi.sub_apply, hΨx]; ring
    rw [e]
    have := vn_add (fun i => φ (x, i) - D.Ψ x.1 i) (cplx (Ψ x.1) - u)
    linarith
  have hsplit : ∑ i, φ (x, i) * h' x.1 i =
      (fun i => φ (x, i) - u i) ⬝ᵥ h' x.1 + ∑ i, u i * h' x.1 i := by
    simp only [dotProduct, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hdot : ‖(fun i => φ (x, i) - u i) ⬝ᵥ h' x.1‖ ≤
      (bgK1 d L N + 1) * δ * vn (h' x.1) :=
    (cNorm_dot_le _ _).trans (mul_le_mul_of_nonneg_right hdiff (vn_nonneg _))
  have hν0 := H.mass
  have hpow : 0 < G.spacing x.1 ^ 2 := by positivity
  have ha := c3a x.1 x.2
  have hb3 := c3b x.1 x.2
  rw [← hspx] at ha hb3
  have ha' : ν * vn (h' x.1) ≤ δ ^ 2 / ε / G.spacing x.1 ^ 2 := by
    rw [le_div_iff₀ hpow]; nlinarith
  have hb' : ν * ‖∑ i, u i * h' x.1 i‖ ≤ δ ^ 2 / G.spacing x.1 ^ 2 := by
    rw [le_div_iff₀ hpow]; nlinarith
  have hK0 := bgK1_pos d L N
  have hterm : ν * ‖(fun i => φ (x, i) - u i) ⬝ᵥ h' x.1‖ ≤
      (bgK1 d L N + 1) * δ ^ 2 / G.spacing x.1 ^ 2 := by
    calc ν * ‖(fun i => φ (x, i) - u i) ⬝ᵥ h' x.1‖
        ≤ ν * ((bgK1 d L N + 1) * δ * vn (h' x.1)) := mul_le_mul_of_nonneg_left hdot hν0
      _ = (bgK1 d L N + 1) * δ * (ν * vn (h' x.1)) := by ring
      _ ≤ (bgK1 d L N + 1) * δ * (δ ^ 2 / ε / G.spacing x.1 ^ 2) :=
          mul_le_mul_of_nonneg_left ha' (by positivity)
      _ ≤ (bgK1 d L N + 1) * δ * (δ / G.spacing x.1 ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine div_le_div_of_nonneg_right ?_ hpow.le
          rw [div_le_iff₀ hε0]; nlinarith
      _ = (bgK1 d L N + 1) * δ ^ 2 / G.spacing x.1 ^ 2 := by ring
  rw [hsplit]
  have := norm_add_le ((fun i => φ (x, i) - u i) ⬝ᵥ h' x.1) (∑ i, u i * h' x.1 i)
  calc ν * ‖(fun i => φ (x, i) - u i) ⬝ᵥ h' x.1 + ∑ i, u i * h' x.1 i‖
      ≤ ν * (‖(fun i => φ (x, i) - u i) ⬝ᵥ h' x.1‖ + ‖∑ i, u i * h' x.1 i‖) :=
        mul_le_mul_of_nonneg_left this hν0
    _ ≤ (bgK1 d L N + 1) * δ ^ 2 / G.spacing x.1 ^ 2 + δ ^ 2 / G.spacing x.1 ^ 2 := by
        rw [mul_add]; exact add_le_add hterm hb'
    _ = _ := by ring

end Balaban.Background
