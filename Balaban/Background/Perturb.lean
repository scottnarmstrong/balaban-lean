/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Def5
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 5.2 (6): perturbations of the data (P2 Cor 3.1)

For data `D` in `Ψ̃^c(δ, ε)` with small solution `(φ, α)` and a second datum `D'` with the same
`h̃` and `Ψ' - Ψ = δΨ`, `|δΨ| ≤ δ₁`: the small solution of `D'` is `(φ + δφ, α + δα)`, where
`(δφ, δα)` is the solution of Proposition 5.1 for `(δΨ, φ̄, α, f₁ = 0)`
(`theorem52_perturb`; `theorem52_perturb_eq` identifies it with `bgFieldC` when `D'` is in `𝒟`).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν δ ε : ℝ} {D : BgData G N}

/-- The source depends affinely on `Ψ`: `S(Ψ + δΨ, h̃) = S(Ψ, h̃) + (Q* a δΨ + 𝔟 δΨ)`. -/
theorem source_perturb (D D' : BgData G N) (hh : D'.h = D.h) (p : G.Ω 1 × Fin N) :
    source G a ν D' p = source G a ν D p +
      pertSource G a (D'.Ψ - D.Ψ) (0 : G.Ω 1 × Fin N → ℂ) p := by
  obtain ⟨x, i⟩ := p
  simp only [source, pertSource, qStar, boundaryTerm, Pi.add_apply, Pi.sub_apply, Pi.zero_apply,
    hh, add_zero]
  have hb : ∀ μ : Fin d,
      ((if (x : Torus d (N₀ * L ^ k)) + Pi.single μ 1 ∈ collar G then
          D'.Ψ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i else 0) +
        (if (x : Torus d (N₀ * L ^ k)) - Pi.single μ 1 ∈ collar G then
          D'.Ψ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i else 0)) =
      ((if (x : Torus d (N₀ * L ^ k)) + Pi.single μ 1 ∈ collar G then
          D.Ψ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i else 0) +
        (if (x : Torus d (N₀ * L ^ k)) - Pi.single μ 1 ∈ collar G then
          D.Ψ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i else 0)) +
      ((if (x : Torus d (N₀ * L ^ k)) + Pi.single μ 1 ∈ collar G then
          D'.Ψ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
            D.Ψ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i else 0) +
        (if (x : Torus d (N₀ * L ^ k)) - Pi.single μ 1 ∈ collar G then
          D'.Ψ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i -
            D.Ψ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i else 0)) := by
    intro μ
    split_ifs <;> ring
  simp only [hb, Finset.sum_add_distrib]
  ring

/-- **Theorem 5.2 (6), perturbations** (P2 Cor 3.1).  Let `D ∈ Ψ̃^c(δ, ε)` (admissible, `δ ≤ c₁`,
`ε ≤ c₀`) with small solution `(φ, α)`, and let `D'` have the same `h̃` with `|Ψ' - Ψ| ≤ δ₁ ≤ δ_*`
on `Ω₁ ∪ C`; assume `K₁ δ ≤ δ_*` (the smallness of Proposition 5.1 for `(δ₀, δ₁) = (K₁ δ, δ₁)`)
and `K₂ δ₁ + K₁ δ < c₀`.  Then `(φ + δφ, α + δα)` is a small solution of `D'`, where `(δφ, δα)` is
the solution of Proposition 5.1 for `(δΨ = Ψ' - Ψ, φ̄, α, f₁ = 0)`; its increments satisfy
`|δφ|₀, |∂δφ|₁, |Δ^D δφ|₂, |δα|₂ ≤ K₂ δ₁`. -/
theorem theorem52_perturb (H : BgHyp d L k ϱ a ν) (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ bgC1 d L N) (hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (hD : InDomainC G ν δ ε D) {D' : BgData G N} (hh : D'.h = D.h) {δ₁ : ℝ} (hδ₁ : 0 ≤ δ₁)
    (hδ₁s : δ₁ ≤ deltaStar d L N) (hK1s : bgK1 d L N * δ ≤ deltaStar d L N)
    (hdΨ : ∀ x ∈ dataSites G, vn (D'.Ψ x - D.Ψ x) ≤ δ₁)
    (hsmall : bgK1 d L N * δ + cK2 d L N * δ₁ < bgC0 d L N)
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hs : IsSmallSolution G a ν (bgC0 d L N) D φ α) :
    ∃ (δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ),
      IsSmallSolution G a ν (bgC0 d L N) D' (φ + δφ) (α + δα) ∧
      SupBounds G δφ (cK2 d L N * δ₁) ∧ Small G δα (cK2 d L N * δ₁) := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨W⟩ := DataWit.exists hD
  obtain ⟨φ1, α1, hs1, hb1, -, hu⟩ := bg_core H hδ0 hδε hε hδ hνε W
  obtain ⟨e1, e2⟩ := hu φ α hs
  subst e1; subst e2
  have hK1 := bgK1_pos d L N
  have hK1δ : 0 ≤ bgK1 d L N * δ := by positivity
  obtain ⟨hδa, -, -, hKc⟩ := bgC1_facts d L N hd0 hδ
  have hc0 := bgC0_le d L N
  -- the hypotheses of Proposition 5.1
  have hunit : ∀ x : G.Ω 1, ∑ i, φ (x, i) * φ (x, i) = 1 := hs1.1.2
  have hbar : ∀ (x : Torus d (N₀ * L ^ k)) (hx : x ∈ G.Ω 1),
      barField G D.Ψ φ x = fun i => φ (⟨x, hx⟩, i) := by
    intro x hx; funext i; simp [barField, hx]
  have hphi : ∀ x ∈ G.Ω 1, vn (barField G D.Ψ φ x) ≤ 3 / 2 := by
    intro x hx
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have h1 := hb1.val ⟨x, hx⟩
    have h2 := W.vn_le hδ0 hxd
    have e : barField G D.Ψ φ x = (fun i => φ (⟨x, hx⟩, i) - D.Ψ x i) + D.Ψ x := by
      rw [hbar x hx]; funext i; simp
    rw [e]
    have := vn_add (fun i => φ (⟨x, hx⟩, i) - D.Ψ x i) (D.Ψ x)
    have := W.P.eps_pos
    have hδ1024 : δ ≤ 1 / 1024 := (approxDelta_le d L hδa).1
    linarith
  have hdot : ∀ y ∈ G.Ω 1, barField G D.Ψ φ y ⬝ᵥ barField G D.Ψ φ y = 1 := by
    intro y hy
    have := hunit ⟨y, hy⟩
    rw [hbar y hy]
    exact this
  have hg0 : ∀ x : G.Ω 1, ‖gdef G (barField G D.Ψ φ) x‖ ≤ δ₁ := by
    intro x
    have e : gdef G (barField G D.Ψ φ) x = 0 := by
      simp only [gdef]
      rw [sub_eq_zero]
      exact hdot x.1 x.2
    rw [e, norm_zero]; exact hδ₁
  have hgl : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
      ‖negLap (zeroExt (G.Ω 1) (gdef G (barField G D.Ψ φ))) (x : Torus d (N₀ * L ^ k))‖ ≤ δ₁ := by
    intro x
    rw [negLap_zeroExt_gdef hdot, norm_zero, mul_zero]; exact hδ₁
  have hyp : Prop51Hyp G a ν α (barField G D.Ψ φ) (D'.Ψ - D.Ψ) (0 : G.Ω 1 × Fin N → ℂ)
      (bgK1 d L N * δ) δ₁ :=
    ⟨H.green, hK1δ, hδ₁, hK1s, hδ₁s, ⟨fun x hx μ => hb1.grad ⟨x, hx⟩ μ,
      fun x hx => hb1.lap ⟨x, hx⟩⟩, hphi, fun x => hb1.alpha x, fun x i => by simpa using hδ₁,
      hdΨ, hg0, hgl⟩
  obtain ⟨δφ, δα, hP, hS, hSup, -⟩ := prop51_exists_unique hd0 hyp
  refine ⟨δφ, δα, ⟨⟨?_, ?_⟩, fun x => ?_⟩, hSup, hS⟩
  · funext p
    have h1 := congrFun hP.1 p
    simp only [Pi.add_apply] at h1
    have hSrc := source_perturb (a := a) (ν := ν) D D' hh p
    have hEL := congrFun hs1.1.1 p
    have hba : barField G D.Ψ φ p.1.1 p.2 = φ p := by simp [barField, p.1.2]
    rw [liftOp_dirichlet_add, show (liftOp N (dirichletOperator G a ν α) *ᵥ (φ + δφ)) p =
      (liftOp N (dirichletOperator G a ν α) *ᵥ φ) p +
        (liftOp N (dirichletOperator G a ν α) *ᵥ δφ) p by rw [Matrix.mulVec_add]; rfl, hEL, hSrc]
    simp only [Pi.add_apply]
    rw [hba] at h1
    linear_combination h1
  · intro x
    have := hP.2 x
    have hba : ∀ i, barField G D.Ψ φ x.1 i = φ (x, i) := fun i => by simp [barField, x.2]
    simp only [hba] at this
    simpa using this
  · calc G.spacing x.1 ^ 2 * ‖(α + δα) x‖ ≤ G.spacing x.1 ^ 2 * (‖α x‖ + ‖δα x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ = G.spacing x.1 ^ 2 * ‖α x‖ + G.spacing x.1 ^ 2 * ‖δα x‖ := by ring
      _ ≤ bgK1 d L N * δ + cK2 d L N * δ₁ := add_le_add (hb1.alpha x) (hS x)
      _ < _ := hsmall

/-- **Theorem 5.2 (6), identification with the background field.**  If moreover `D'` lies in the
union domain `𝒟`, then `(bgFieldC D', bgMultC D') = (bgFieldC D + δφ, bgMultC D + δα)` with the
increments of Proposition 5.1 (bounded by `K₂ δ₁`). -/
theorem theorem52_perturb_eq (H : BgHyp d L k ϱ a ν) (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ bgC1 d L N) (hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (hD : InDomainC G ν δ ε D) {D' : BgData G N}
    (hD' : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D') (hh : D'.h = D.h) {δ₁ : ℝ}
    (hδ₁ : 0 ≤ δ₁) (hδ₁s : δ₁ ≤ deltaStar d L N) (hK1s : bgK1 d L N * δ ≤ deltaStar d L N)
    (hdΨ : ∀ x ∈ dataSites G, vn (D'.Ψ x - D.Ψ x) ≤ δ₁)
    (hsmall : bgK1 d L N * δ + cK2 d L N * δ₁ < bgC0 d L N) :
    ∃ (δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ),
      SupBounds G δφ (cK2 d L N * δ₁) ∧ Small G δα (cK2 d L N * δ₁) ∧
      bgFieldC G a ν (bgC0 d L N) D' = bgFieldC G a ν (bgC0 d L N) D + δφ ∧
      bgMultC G a ν (bgC0 d L N) D' = bgMultC G a ν (bgC0 d L N) D + δα := by
  have hDU : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D := ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hD⟩
  obtain ⟨φ, α, hs, hu⟩ := exists_small_of_union H hDU
  obtain ⟨hf, hm⟩ := bgFieldC_eq hs hu
  obtain ⟨φ', α', hs', hu'⟩ := exists_small_of_union H hD'
  obtain ⟨hf', hm'⟩ := bgFieldC_eq hs' hu'
  obtain ⟨δφ, δα, hsol, hsup, hsm⟩ := theorem52_perturb H hδ0 hδε hε hδ hνε hD hh hδ₁ hδ₁s hK1s hdΨ
    hsmall hs
  have e := hu' _ _ hsol
  refine ⟨δφ, δα, hsup, hsm, ?_, ?_⟩
  · rw [hf', hf, ← e.1]
  · rw [hm', hm, ← e.2]

end Balaban.Background
