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
# Theorem 5.2 (2): analyticity of the small solution in the data

The map `p = (Ψ, h̃) ↦ (φ₀(p), 0, 0, f₀(p))` of raw data into the data space `Edat` of Proposition
5.1 (`rawQ`) is analytic on `approxDomain` (Lemma 5.3 (d)), and `prop51_analytic` gives the
analytic solution operator on the open set `StrictData`.  `theorem52_analytic` combines them:
one function `F` of the raw data (all pairs of fields `Torus → ℂ^N`) which is analytic at every
point `(D.Ψ, D.h)` of the union domain `𝒟` and returns the small solution there.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Strict

variable {G : GeneratingSet d L N₀ k ϱ}

/-- Strict inequalities from non-strict ones with room to spare. -/
theorem StrictData.of_hyp {a : ℕ → ℝ} {ν : ℝ} {p : Edat G N} {δ₀ δ₁ δ₀' δ₁' : ℝ}
    (h : Prop51Hyp G a ν p.2.1 p.1 p.2.2.1 p.2.2.2 δ₀ δ₁)
    (hφ : ∀ x : G.Ω 1, vn (p.1 x) < 3 / 2) (h0 : δ₀ < δ₀') (h1 : δ₁ < δ₁') :
    StrictData G N δ₀' δ₁' p := by
  have hℓ : ∀ x : G.Ω 1, 0 < G.spacing (x : Torus d (N₀ * L ^ k)) := fun x => spacing_pos G
  refine ⟨fun x μ => ⟨?_, ?_⟩, fun x => ?_, hφ, fun x => ?_, fun x i => ?_, fun x => ?_,
    fun x => ?_, fun x => ?_⟩
  · exact lt_of_le_of_lt (h.smooth.grad x x.2 μ).1 (div_lt_div_of_pos_right h0 (hℓ x))
  · exact lt_of_le_of_lt (h.smooth.grad x x.2 μ).2 (div_lt_div_of_pos_right h0 (hℓ x))
  · exact lt_of_le_of_lt (h.smooth.lap x x.2)
      (div_lt_div_of_pos_right h0 (by have := hℓ x; positivity))
  · exact lt_of_le_of_lt (h.alpha0 x) h0
  · exact lt_of_le_of_lt (h.f₁_bd x i) h1
  · exact lt_of_le_of_lt (h.dPsi x x.2) h1
  · exact lt_of_le_of_lt (h.g0 x) h1
  · exact lt_of_le_of_lt (h.gl x) h1

end Strict

section Analytic

variable (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ)

/-- The data of Proposition 5.1 attached to raw data `p = (Ψ, h̃)`: `(φ₀, α₀, δΨ, f₁) =
(approxField, 0, 0, S - H_D(0) φ₀)`. -/
noncomputable def rawQ (p : RawData d L N₀ k N) : Edat G N :=
  (approxField G a ν p.1 p.2, 0, 0,
    fun r => residualRaw G a ν p.1 p.2 (approxField G a ν p.1 p.2) r.1 r.2)

theorem rawQ_residual (D : BgData G N) :
    (rawQ G a ν ((D.Ψ, D.h) : RawData d L N₀ k N)).2.2.2 =
      residual G a ν D (approxField G a ν D.Ψ D.h) := by
  funext r
  exact (residual_eq_raw G a ν D _ r.1 r.2).symm

theorem analyticAt_rawQ {p : RawData d L N₀ k N} (hp : p ∈ approxDomain G a ν) :
    AnalyticAt ℂ (rawQ G a ν) p := by
  classical
  refine AnalyticAt.prod ?_ (AnalyticAt.prod analyticAt_const (AnalyticAt.prod analyticAt_const ?_))
  · refine analyticAt_pi_iff.2 fun y => analyticAt_pi_iff.2 fun i => ?_
    by_cases hy : y ∈ dataSites G
    · exact approxField_analytic G a ν hy i p hp
    · have : (fun q : RawData d L N₀ k N => approxField G a ν q.1 q.2 y i) = fun _ => 0 := by
        funext q
        have h1 : y ∉ G.Ω 1 := fun h => hy ((mem_dataSites G).2 (Or.inl h))
        have h2 : y ∉ collar G := fun h => hy ((mem_dataSites G).2 (Or.inr h))
        simp [approxField, h1, h2]
      rw [this]; exact analyticAt_const
  · exact analyticAt_pi_iff.2 fun r => residualRaw_analytic G a ν r.1 r.2 p hp

end Analytic

section Main

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem strictData_rawQ {δ ε : ℝ} {D : BgData G N} (H : BgHyp d L k ϱ a ν)
    (S : ApproxSetting d L k ϱ a ν δ ε) (hδa : δ ≤ approxDelta d L) (W : DataWit G ν δ ε D)
    (h2 : 2 * (lemma53Const d L * δ) ≤ deltaStar d L N) (hC32 : lemma53Const d L * δ ≤ 1 / 32) :
    StrictData G N (deltaStar d L N) (deltaStar d L N)
      (rawQ G a ν ((D.Ψ, D.h) : RawData d L N₀ k N)) := by
  have hC0 := lemma53Const_pos d L
  have hCδ : 0 < lemma53Const d L * δ := by have := S.hδ0; positivity
  have hyp := prop51Hyp_of_data (N := N) H S hδa W (by linarith) hC32
  have hq : rawQ G a ν ((D.Ψ, D.h) : RawData d L N₀ k N) =
      (approxField G a ν D.Ψ D.h, 0, 0, residual G a ν D (approxField G a ν D.Ψ D.h)) :=
    Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (rawQ_residual G a ν D)))
  rw [hq]
  exact StrictData.of_hyp (p := (approxField G a ν D.Ψ D.h, 0, 0,
      residual G a ν D (approxField G a ν D.Ψ D.h))) hyp
    (fun x => phi0_vn_lt S hδa W hC32 ((mem_dataSites G).2 (Or.inl x.2))) (by linarith)
    (by linarith)

theorem analyticAt_approx_coord {p : RawData d L N₀ k N} (hp : p ∈ approxDomain G a ν)
    (y : Torus d (N₀ * L ^ k)) (i : Fin N) :
    AnalyticAt ℂ (fun q : RawData d L N₀ k N => approxField G a ν q.1 q.2 y i) p := by
  classical
  by_cases hy : y ∈ dataSites G
  · exact approxField_analytic G a ν hy i p hp
  · have : (fun q : RawData d L N₀ k N => approxField G a ν q.1 q.2 y i) = fun _ => 0 := by
      funext q
      have h1 : y ∉ G.Ω 1 := fun h => hy ((mem_dataSites G).2 (Or.inl h))
      have h2 : y ∉ collar G := fun h => hy ((mem_dataSites G).2 (Or.inr h))
      simp [approxField, h1, h2]
    rw [this]; exact analyticAt_const

/-- **Theorem 5.2 (2), analyticity.**  There is one function `F` of the raw data
`(Ψ, h̃) ∈ (Torus → ℂ^N)²`, analytic at every point `(D.Ψ, D.h)` for `D` in the union domain
`𝒟(G, a, ν)`, which returns the small solution `(φ, α)` of (EL) at such a point.  (The solution
depends analytically on the data in the ambient space of all fields, not only on the layer-constant
subspace in which `𝒟` sits.) -/
theorem theorem52_analytic (H : BgHyp d L k ϱ a ν) :
    ∃ F : RawData d L N₀ k N → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
      AnalyticOnNhd ℂ F {p | ∃ D : BgData G N,
        InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)} ∧
      ∀ (D : BgData G N), InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D →
        ∀ (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ),
          IsSmallSolution G a ν (bgC0 d L N) D φ α → F (D.Ψ, D.h) = (φ, α) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hds : 0 < deltaStar d L N := deltaStar_pos d L N hd0
  obtain ⟨sol, hsolan, hsolprop⟩ := prop51_analytic (N := N) hd0 (H.green (G := G))
    hds.le hds.le le_rfl le_rfl
  refine ⟨fun p => (fun r => approxField G a ν p.1 p.2 r.1 r.2 + (sol (rawQ G a ν p)).1 r,
    (sol (rawQ G a ν p)).2), ?_, ?_⟩
  · rintro p ⟨D, ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩, rfl⟩
    obtain ⟨W⟩ := DataWit.exists hDC
    obtain ⟨hδa, h2, hC32, -⟩ := bgC1_facts d L N hd0 hδc
    have S : ApproxSetting d L k ϱ a ν δ ε :=
      H.approxSetting hδ0 hδε (hε.trans (bgC0_le d L N)) (approxDelta_le d L hδa).1 hνε
    have hp0 := data_mem_approxDomain S W hδa
    have hq := analyticAt_rawQ G a ν hp0
    have hsol := hsolan _ (strictData_rawQ H S hδa W h2 hC32)
    have hcomp := hsol.comp hq
    refine AnalyticAt.prod (analyticAt_pi_iff.2 fun r => ?_) (analyticAt_snd.comp hcomp)
    exact (analyticAt_approx_coord hp0 _ _).add
      (analyticAt_pi_iff.1 (analyticAt_fst.comp hcomp) r)
  · rintro D ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ φ α hs
    obtain ⟨W⟩ := DataWit.exists hDC
    obtain ⟨hδa, h2, hC32, -⟩ := bgC1_facts d L N hd0 hδc
    have S : ApproxSetting d L k ϱ a ν δ ε :=
      H.approxSetting hδ0 hδε (hε.trans (bgC0_le d L N)) (approxDelta_le d L hδa).1 hνε
    have hStrict := strictData_rawQ H S hδa W h2 hC32
    obtain ⟨hP, hSm⟩ := perturbed_of_small (bgC0_le_c6 d L N) (approxField G a ν D.Ψ D.h) hs
    obtain ⟨-, -, -, huniq⟩ := hsolprop _ hStrict
    have hP' : IsPerturbed G a ν (rawQ G a ν ((D.Ψ, D.h) : RawData d L N₀ k N)).2.1
        (rawQ G a ν ((D.Ψ, D.h) : RawData d L N₀ k N)).1
        (pertSource G a (rawQ G a ν ((D.Ψ, D.h) : RawData d L N₀ k N)).2.2.1
          (rawQ G a ν ((D.Ψ, D.h) : RawData d L N₀ k N)).2.2.2)
        (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2) α := by
      have e1 : (rawQ G a ν ((D.Ψ, D.h) : RawData d L N₀ k N)).2.2.1 =
          (0 : Torus d (N₀ * L ^ k) → Fin N → ℂ) := rfl
      rw [e1, pertSource_zero, rawQ_residual]
      exact hP
    obtain ⟨e1, e2⟩ := huniq _ _ hP' hSm
    refine Prod.ext ?_ ?_
    · funext r
      have := congrFun e1 r
      simp only at this ⊢
      linear_combination -this
    · exact e2.symm

end Main

end Balaban.Background
