/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Minimizer
public import Balaban.Background.Theorem52Analytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Def-5: the background fields and their characterization theorems (BACKGROUND.md §7)

* `bgField`, `bgMult`: the unique global minimizer of the action on `(S^{N-1})^{Ω₁}` and its
  Lagrange multiplier, for real data (`dite` on `∃! φ, IsMinimizer ...`);
* `bgFieldC c₀`, `bgMultC c₀`: the unique small solution of (EL) with `|α|₂ < c₀`, for complex
  data (`dite` on `∃! s, IsSmallSolution c₀ ...`).

Rule 4 of `AGENTS.md`: the definitions are made through `∃!` and land together with their
characterization theorems: `theorem71` (real data: the `∃!` holds, the values are the small
solution, the bounds P2 (1.15), (5.3)) and `theorem72` (complex data: the `∃!` holds, the values
satisfy the predicate and the bounds, are analytic in the data and agree with `bgField` on real
data).  No `Classical.choose` is taken from mere existence.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Defs

variable (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ)

/-- **Def-5(a), the real background field**: the unique global minimizer of the action on
`(S^{N-1})^{Ω₁}` for real data (`IsMinimizer`), and `0` when there is no unique minimizer.
`theorem71` shows that the `∃!` holds on the real domain `𝒟_ℝ` and that the value there is the
small solution of (EL). -/
noncomputable def bgField (D : BgData G N) : G.Ω 1 × Fin N → ℂ := by
  classical
  exact if H : ∃! φ : G.Ω 1 × Fin N → ℂ, IsMinimizer G a ν D φ then H.exists.choose else 0

/-- **Def-5(a), the multiplier** `α = -φ · (H_D(0) φ - S)` of the background field `φ = bgField`. -/
noncomputable def bgMult (D : BgData G N) (x : G.Ω 1) : ℂ :=
  -∑ i, bgField G a ν D (x, i) *
    ((liftOp N (dirichletOperator G a ν 0) *ᵥ bgField G a ν D - source G a ν D) (x, i))

/-- **Def-5(b), the complex background field** with the parameter `c₀`: the unique small solution
`(φ, α)` of (EL) with `|α|₂ < c₀` (`IsSmallSolution c₀`), and `0` if there is none or several.
`theorem72` shows that the `∃!` holds on the complex domain `𝒟` for `c₀ = bgC0`. -/
noncomputable def bgFieldC (c₀ : ℝ) (D : BgData G N) : G.Ω 1 × Fin N → ℂ := by
  classical
  exact if H : ∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsSmallSolution G a ν c₀ D s.1 s.2
    then H.exists.choose.1 else 0

/-- **Def-5(b), the complex multiplier** `α` of the small solution. -/
noncomputable def bgMultC (c₀ : ℝ) (D : BgData G N) : G.Ω 1 → ℂ := by
  classical
  exact if H : ∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsSmallSolution G a ν c₀ D s.1 s.2
    then H.exists.choose.2 else 0

variable {G a ν}

theorem bgField_eq {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ} (h : IsMinimizer G a ν D φ)
    (hu : ∀ φ', IsMinimizer G a ν D φ' → φ' = φ) : bgField G a ν D = φ := by
  classical
  have H : ∃! φ : G.Ω 1 × Fin N → ℂ, IsMinimizer G a ν D φ := ⟨φ, h, hu⟩
  unfold bgField
  simp only [H, ↓reduceDIte]
  exact H.unique H.exists.choose_spec h

theorem bgFieldC_eq {c₀ : ℝ} {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (h : IsSmallSolution G a ν c₀ D φ α)
    (hu : ∀ φ' α', IsSmallSolution G a ν c₀ D φ' α' → φ' = φ ∧ α' = α) :
    bgFieldC G a ν c₀ D = φ ∧ bgMultC G a ν c₀ D = α := by
  classical
  have H : ∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsSmallSolution G a ν c₀ D s.1 s.2 :=
    ⟨(φ, α), h, fun s hs => Prod.ext (hu s.1 s.2 hs).1 (hu s.1 s.2 hs).2⟩
  have e : H.exists.choose = (φ, α) := H.unique H.exists.choose_spec h
  refine ⟨?_, ?_⟩
  · unfold bgFieldC; simp only [H, ↓reduceDIte]; rw [e]
  · unfold bgMultC; simp only [H, ↓reduceDIte]; rw [e]

/-- On a solution of (EL) with `φ · φ = 1`, the multiplier formula returns `α`. -/
theorem mult_formula {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (h : IsEL G a ν D φ α) (x : G.Ω 1) :
    -∑ i, φ (x, i) * ((liftOp N (dirichletOperator G a ν 0) *ᵥ φ - source G a ν D) (x, i)) =
      α x := by
  have hS : ∀ p, source G a ν D p = (liftOp N (dirichletOperator G a ν 0) *ᵥ φ) p + α p.1 * φ p := by
    intro p
    rw [← h.1, H_alpha_apply]
  have e : ∀ i, φ (x, i) * ((liftOp N (dirichletOperator G a ν 0) *ᵥ φ - source G a ν D) (x, i)) =
      -(α x * (φ (x, i) * φ (x, i))) := by
    intro i
    rw [Pi.sub_apply, hS (x, i)]; ring
  simp only [e, Finset.sum_neg_distrib, neg_neg, ← Finset.mul_sum, h.2 x, mul_one]

end Defs

section Real

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem isReal_of_inDomainR {δ : ℝ} {D : BgData G N} (hD : InDomainR G ν δ D) : D.IsReal := by
  obtain ⟨Ψ, h, -, hΨ, hh⟩ := hD
  intro x i
  constructor
  · by_cases hx : x ∈ dataSites G
    · rw [hΨ x hx i]; simp
    · rw [D.Ψ_zero x hx]; simp
  · by_cases hx : x ∈ G.Ω 1
    · rw [hh x hx i]; simp
    · rw [D.h_zero x hx]; simp

/-- **Real data**: existence, bounds, uniqueness in the class `|α|₂ < c₀`, realness, and the unique
global minimizer. -/
theorem bg_real (H : BgHyp d L k ϱ a ν) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ bgC1 d L N)
    {D : BgData G N} (hD : InDomainR G ν δ D) :
    ∃ (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ),
      IsSmallSolution G a ν (bgC0 d L N) D φ α ∧ BgBounds G D φ α (bgK1 d L N * δ) ∧
      (∀ (φ' : G.Ω 1 × Fin N → ℂ) (α' : G.Ω 1 → ℂ),
        IsSmallSolution G a ν (bgC0 d L N) D φ' α' → φ' = φ ∧ α' = α) ∧
      IsRealUnitField G φ ∧ IsMinimizer G a ν D φ ∧
      (∀ φ', IsMinimizer G a ν D φ' → φ' = φ) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hreal := isReal_of_inDomainR hD
  obtain ⟨Ψ, h₀, hP, hΨ, hh⟩ := hD
  have hδc0 : δ ≤ bgC0 d L N := hδ.trans (bgC1_le_bgC0 d L N hd0)
  have W := DataWit.ofReal hδ0 hδ0 hP D hΨ hh
  have hνε : ν * ((L : ℝ) ^ k) ^ 2 * δ ^ 2 ≤ δ ^ 2 := by
    have := H.massLe
    nlinarith [sq_nonneg δ]
  obtain ⟨φ, α, hs, hb, -, hu⟩ := bg_core H hδ0 le_rfl hδc0 hδ hνε W
  have hcj := isSmallSolution_conj D hreal hs
  have hφre : ∀ (x : G.Ω 1) i, (φ (x, i)).im = 0 := fun x i => by
    have := congrFun (hu _ _ hcj).1 (x, i)
    rw [← Complex.conj_eq_iff_im]; exact this
  have hunit : IsRealUnitField G φ := isRealUnit_of_dot hφre hs.1.2
  refine ⟨φ, α, hs, hb, hu, hunit, ?_, ?_⟩
  · exact isMinimizer_of_smallSolution (bgC0_le d L N) H.mass H.weights D hreal hs hunit
  · intro φ' hφ'
    exact eq_of_isMinimizer (bgC0_le d L N) H.mass H.weights D hreal hs hunit hφ'

end Real

section Theorems

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem existsUnique_of {c₀ : ℝ} {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (h : IsSmallSolution G a ν c₀ D φ α)
    (hu : ∀ φ' α', IsSmallSolution G a ν c₀ D φ' α' → φ' = φ ∧ α' = α) :
    ∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsSmallSolution G a ν c₀ D s.1 s.2 :=
  ⟨(φ, α), h, fun s hs => Prod.ext (hu s.1 s.2 hs).1 (hu s.1 s.2 hs).2⟩

/-- **Theorem 7.1 (real data; Theorem 5.2 (1), (3), (4)).**  Let `ν ≥ 0`, `(G, a, ν)` satisfy
`BgHyp` and let `D` be real data in the real domain `𝒟_ℝ` (`δ ≤ c₁`).  Then:

* the global minimizer of the action on `(S^{N-1})^{Ω₁}` exists and is unique (`∃!`);
* `bgField` is a real unit field, and `(bgField, bgMult)` is the small solution of (EL)
  (`IsSmallSolution c₀`, `c₀ = bgC0`);
* the bounds P2 (1.15) hold with the constant `K₁ δ` for every `δ ≤ c₁` with `D ∈ Ψ̃(δ)`;
* the identity (5.3) and its coercive lower bound: for every real unit field `σ`,
  `A(σ) - A(φ) = ½ ∑_i Re ⟨σ_i - φ_i, H_D(α)(σ_i - φ_i)⟩ ≥ (7/32) ∑_i ‖ℓ⁻¹(σ_i - φ_i)‖²`. -/
theorem theorem71 (H : BgHyp d L k ϱ a ν) {D : BgData G N}
    (hD : InUnionDomainR G (bgC1 d L N) ν D) :
    (∃! φ : G.Ω 1 × Fin N → ℂ, IsMinimizer G a ν D φ) ∧
    IsRealUnitField G (bgField G a ν D) ∧
    IsSmallSolution G a ν (bgC0 d L N) D (bgField G a ν D) (bgMult G a ν D) ∧
    (∀ σ : G.Ω 1 × Fin N → ℂ, IsRealUnitField G σ →
      action G a ν D σ - action G a ν D (bgField G a ν D) =
          (1 / 2) * ∑ i, Green.reQuad (dirichletOperator G a ν (bgMult G a ν D))
            (fun x => σ (x, i) - bgField G a ν D (x, i)) ∧
        (7 / 32) * ∑ i, weightedSqNorm G (fun x => σ (x, i) - bgField G a ν D (x, i)) ≤
          action G a ν D σ - action G a ν D (bgField G a ν D)) ∧
    (∀ δ : ℝ, 0 < δ → δ ≤ bgC1 d L N → InDomainR G ν δ D →
      BgBounds G D (bgField G a ν D) (bgMult G a ν D) (bgK1 d L N * δ)) := by
  obtain ⟨δ₀, hδ₀, hδ₀c, hD₀⟩ := hD
  obtain ⟨φ, α, hs, -, hu, hunit, hmin, hmu⟩ := bg_real H hδ₀ hδ₀c hD₀
  have hreal := isReal_of_inDomainR hD₀
  have hf : bgField G a ν D = φ := bgField_eq hmin hmu
  have hm : bgMult G a ν D = α := by
    funext x
    unfold bgMult
    rw [hf]
    exact mult_formula hs.1 x
  rw [hf, hm]
  refine ⟨⟨φ, hmin, hmu⟩, hunit, hs, fun σ hσ => ?_, fun δ hδ hδc hDδ => ?_⟩
  · exact action_sub_ge (bgC0_le d L N) H.mass H.weights D hreal hs hunit hσ
  · obtain ⟨φ', α', hs', hb', -, -, hmin', -⟩ := bg_real H hδ hδc hDδ
    have e := hmu φ' hmin'
    have e2 := (hu φ' α' hs')
    rw [e2.1, e2.2] at hb'
    exact hb'

/-- A small solution exists for every datum of the complex union domain `𝒟`. -/
theorem exists_small_of_union (H : BgHyp d L k ϱ a ν) {D : BgData G N}
    (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D) :
    ∃ (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ),
      IsSmallSolution G a ν (bgC0 d L N) D φ α ∧
      (∀ (φ' : G.Ω 1 × Fin N → ℂ) (α' : G.Ω 1 → ℂ),
        IsSmallSolution G a ν (bgC0 d L N) D φ' α' → φ' = φ ∧ α' = α) := by
  obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hD
  obtain ⟨W⟩ := DataWit.exists hDC
  obtain ⟨φ, α, hs, -, -, hu⟩ := bg_core H hδ0 hδε hε hδc hνε W
  exact ⟨φ, α, hs, hu⟩

/-- **Theorem 7.2 (complex data; Theorem 5.2 (1), (3)).**  For data in the open union domain `𝒟`
(`InUnionDomainC (bgC0) (bgC1)`): the small solution of (EL) with `|α|₂ < c₀` exists and is
unique (`∃!`); `(bgFieldC, bgMultC)` is that solution; and it satisfies the bounds P2 (1.15) with
the constant `K₁ δ` for every admissible `(δ, ε)` with `D ∈ Ψ̃^c(δ, ε)`. -/
theorem theorem72 (H : BgHyp d L k ϱ a ν) {D : BgData G N}
    (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D) :
    (∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsSmallSolution G a ν (bgC0 d L N) D s.1 s.2) ∧
    IsSmallSolution G a ν (bgC0 d L N) D (bgFieldC G a ν (bgC0 d L N) D)
      (bgMultC G a ν (bgC0 d L N) D) ∧
    (∀ δ ε : ℝ, 0 < δ → δ ≤ ε → ε ≤ bgC0 d L N → δ ≤ bgC1 d L N →
      ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2 → InDomainC G ν δ ε D →
      BgBounds G D (bgFieldC G a ν (bgC0 d L N) D) (bgMultC G a ν (bgC0 d L N) D)
        (bgK1 d L N * δ)) := by
  obtain ⟨φ, α, hs, hu⟩ := exists_small_of_union H hD
  obtain ⟨hf, hm⟩ := bgFieldC_eq hs hu
  rw [hf, hm]
  refine ⟨existsUnique_of hs hu, hs, fun δ ε hδ0 hδε hε hδc hνε hDC => ?_⟩
  obtain ⟨W⟩ := DataWit.exists hDC
  obtain ⟨φ', α', hs', hb', -, hu'⟩ := bg_core H hδ0 hδε hε hδc hνε W
  have e := hu φ' α' hs'
  rw [e.1, e.2] at hb'
  exact hb'

/-- **Theorem 7.2, analyticity** (Theorem 5.2 (2)).  There is one function `F` of the raw data
`(Ψ, h̃)`, analytic at every point `(D.Ψ, D.h)` with `D` in the union domain `𝒟`, which returns
`(bgFieldC, bgMultC)` there. -/
theorem theorem72_analytic (H : BgHyp d L k ϱ a ν) :
    ∃ F : RawData d L N₀ k N → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
      AnalyticOnNhd ℂ F {p | ∃ D : BgData G N,
        InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)} ∧
      ∀ D : BgData G N, InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D →
        F (D.Ψ, D.h) = (bgFieldC G a ν (bgC0 d L N) D, bgMultC G a ν (bgC0 d L N) D) := by
  obtain ⟨F, hF, hFe⟩ := theorem52_analytic (G := G) (a := a) (ν := ν) H
  refine ⟨F, hF, fun D hD => ?_⟩
  obtain ⟨φ, α, hs, hu⟩ := exists_small_of_union H hD
  obtain ⟨hf, hm⟩ := bgFieldC_eq hs hu
  rw [hf, hm]
  exact hFe D hD φ α hs

/-- **Theorem 7.2, agreement with the real field**: on real data of `𝒟_ℝ`, `bgFieldC c₀` is
`bgField` and `bgMultC c₀` is `bgMult`. -/
theorem theorem72_real (H : BgHyp d L k ϱ a ν) {D : BgData G N}
    (hD : InUnionDomainR G (bgC1 d L N) ν D) :
    bgFieldC G a ν (bgC0 d L N) D = bgField G a ν D ∧
      bgMultC G a ν (bgC0 d L N) D = bgMult G a ν D := by
  obtain ⟨δ₀, hδ₀, hδ₀c, hD₀⟩ := hD
  obtain ⟨φ, α, hs, -, hu, -, hmin, hmu⟩ := bg_real H hδ₀ hδ₀c hD₀
  obtain ⟨hf, hm⟩ := bgFieldC_eq hs hu
  have hf' : bgField G a ν D = φ := bgField_eq hmin hmu
  have hm' : bgMult G a ν D = α := by
    funext x
    unfold bgMult
    rw [hf']
    exact mult_formula hs.1 x
  rw [hf, hm, hf', hm']
  exact ⟨rfl, rfl⟩

end Theorems

end Balaban.Background
