/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ExistenceBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 5.2 (1), (3): existence, bounds and uniqueness (BACKGROUND.md §5.4)

For data `D` in the complex domain `Ψ̃^c(δ, ε)` with `δ ≤ c₁`, `ε ≤ c₀`, `ν L^{2k} ε² ≤ δ²`:
`φ = φ₀ + δφ`, `α = δα`, with `φ₀` the approximate field of Lemma 5.3 (`α₀ = 0`) and `(δφ, δα)`
the solution of Proposition 5.1 for `δΨ = 0`, `f₁ = S - H_D(0) φ₀` (`bg_core`).

* existence of a small solution (`IsSmallSolution c₀`), with the bounds P2 (1.15) (`BgBounds`)
  with constant `K₁ δ`;
* uniqueness among all solutions of (EL) with `|α|₂ < c₀` (strict class);
* the field differs from the approximate field by an increment with sup bounds.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Core

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν δ ε : ℝ} {D : BgData G N}

theorem approx_data_close (S : ApproxSetting d L k ϱ a ν δ ε) (hδa : δ ≤ approxDelta d L)
    (W : DataWit G ν δ ε D) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) :
    vn (approxField G a ν D.Ψ D.h y - D.Ψ y) ≤ lemma53Const d L * δ := by
  obtain ⟨g1, -⟩ := lemma53 S hδa D W.real W (fun x hx i => W.real_Ψ hx i)
    (fun x hx i => W.real_h hx i)
  exact (g1 y hy).2

theorem perturbed_of_small {c₀ : ℝ} (hc : c₀ ≤ c6 d L N) {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (h : IsSmallSolution G a ν c₀ D φ α) :
    IsPerturbed G a ν (0 : G.Ω 1 → ℂ) φ₀ (residual G a ν D φ₀)
      (fun p => φ p - φ₀ p.1 p.2) α ∧ Small G α (c6 d L N) := by
  obtain ⟨hEL, hα⟩ := h
  refine ⟨(isPerturbed_iff_isEL D φ₀ _ α).2 (by convert hEL using 2; ring), fun x => ?_⟩
  exact ((hα x).trans_le hc).le

/-- The approximate field is bounded by `5/4` on the data sites. -/
theorem phi0_vn_lt (S : ApproxSetting d L k ϱ a ν δ ε) (hδa : δ ≤ approxDelta d L)
    (W : DataWit G ν δ ε D) (hC32 : lemma53Const d L * δ ≤ 1 / 32)
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) : vn (approxField G a ν D.Ψ D.h y) < 3 / 2 := by
  have h1 := approx_data_close S hδa W hy
  have h2 := W.vn_le S.hδ0 hy
  have e : approxField G a ν D.Ψ D.h y = (approxField G a ν D.Ψ D.h y - D.Ψ y) + D.Ψ y := by
    funext i; simp
  rw [e]
  have h3 := vn_add (approxField G a ν D.Ψ D.h y - D.Ψ y) (D.Ψ y)
  have := S.hε; have := S.hδ
  linarith

/-- **Existence, bounds and uniqueness** (Theorem 5.2 (1), (3) for one decomposition `W`). -/
theorem bg_core (H : BgHyp d L k ϱ a ν) (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N)
    (hδ : δ ≤ bgC1 d L N) (hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (W : DataWit G ν δ ε D) :
    ∃ (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ),
      IsSmallSolution G a ν (bgC0 d L N) D φ α ∧
      BgBounds G D φ α (bgK1 d L N * δ) ∧
      SupBounds G (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2)
        (cK2 d L N * (lemma53Const d L * δ)) ∧
      (∀ (φ' : G.Ω 1 × Fin N → ℂ) (α' : G.Ω 1 → ℂ),
        IsSmallSolution G a ν (bgC0 d L N) D φ' α' → φ' = φ ∧ α' = α) := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨hδa, h2, hC32, hK⟩ := bgC1_facts d L N hd0 hδ
  have hC0 := lemma53Const_pos d L
  have hCδ : 0 ≤ lemma53Const d L * δ := by positivity
  have hdelta := approxDelta_le d L hδa
  have S : ApproxSetting d L k ϱ a ν δ ε :=
    H.approxSetting hδ0 hδε (hε.trans (bgC0_le d L N)) hdelta.1 hνε
  have hyp := prop51Hyp_of_data (N := N) H S hδa W (by linarith) hC32
  obtain ⟨δφ, δα, hP, hS, hSup, huniq⟩ := prop51_exists_unique hd0 hyp
  rw [pertSource_zeroΨ] at hP huniq
  have hc0 := bgC0_pos d L N hd0
  have hK2 := cK2_pos d L N
  have hKδ : cK2 d L N * (lemma53Const d L * δ) ≤ bgK1 d L N * δ := by
    unfold bgK1
    have : 0 ≤ (1 + L + 2 * d * (L : ℝ) ^ 2 + 2 * N * cK2 d L N) * (lemma53Const d L * δ) := by
      positivity
    nlinarith
  refine ⟨fun p => approxField G a ν D.Ψ D.h p.1 p.2 + δφ p, δα,
    ⟨(isPerturbed_iff_isEL D _ δφ δα).1 hP, fun x => ?_⟩, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt ((hS x).trans hKδ) (by linarith)
  · refine bgBounds_of_parts (H.green (G := G)).sep_gt_one (by have := H.hL; omega) hCδ
      (by positivity) ?_ (fun y hy => approx_data_close S hδa W hy) hSup
      (fun x => (hS x).trans hKδ) ?_
    · exact (lemma53 S hδa D W.real W (fun x hx i => W.real_Ψ hx i)
        (fun x hx i => W.real_h hx i)).2.1
    · unfold bgK1
      have : 0 ≤ (N : ℝ) * (cK2 d L N * (lemma53Const d L * δ)) := by positivity
      nlinarith
  · simpa using hSup
  · intro φ' α' hsol
    obtain ⟨hEL, hα'⟩ := hsol
    have hper := (isPerturbed_iff_isEL (a := a) (ν := ν) D (approxField G a ν D.Ψ D.h)
      (fun p => φ' p - approxField G a ν D.Ψ D.h p.1 p.2) α').2 (by
        convert hEL using 2; ring)
    have hsm : Small G α' (c6 d L N) := fun x =>
      ((hα' x).trans_le (bgC0_le_c6 d L N)).le
    obtain ⟨e1, e2⟩ := huniq _ _ hper hsm
    refine ⟨?_, e2⟩
    funext p
    have := congrFun e1 p
    linear_combination this

end Core

end Balaban.Background
