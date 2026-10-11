/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Def5
public import Balaban.Multiscale.HolderGlobal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# I-1(e): the Hölder bound for the increment `bgFieldC - approxField` (BACKGROUND.md §5.2)

The (EL) equation gives `H_D(α) (φ - φ₀) = f₀ - α φ₀`, with `f₀` the residual of the approximate
field `φ₀` of Lemma 5.3, so that `φ - φ₀ = G(α) (f₀ - α φ₀)` componentwise, `|f₀ - α φ₀|₂ ≤ (C₃ +
(3/2) K₁) δ`.  The landed Hölder estimate `global_g2iv` (G-2(iii), P2 (3.17)) then bounds the
Hölder seminorm `|∂(φ - φ₀)|_{(θ),2-θ}` of the increment by `(B/θ) (C₃ + (3/2) K₁) δ`, with `B`
depending on `(d, L)` only.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L : ℕ} [NeZero L]

/-- **I-1(e), the increment part.**  For the small solution `φ = bgFieldC` of data in `Ψ̃^c(δ, ε)`
and the approximate field `φ₀ = approxField` of Lemma 5.3, every component of the zero extension
of `φ - φ₀` has Hölder seminorm `|∂(φ - φ₀)|_{(θ),2-θ} ≤ (B/θ) (C₃ + (3/2) K₁) δ`, `B = B(d, L)`. -/
theorem bgFieldC_increment_holder (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ {N k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ}
      (G : GeneratingSet d L N₀ k ϱ) {a : ℕ → ℝ} {ν : ℝ}, BgHyp d L k ϱ a ν →
      ∀ {D : BgData G N} {δ ε : ℝ}, 0 < δ → δ ≤ ε → ε ≤ bgC0 d L N → δ ≤ bgC1 d L N →
      ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2 → InDomainC G ν δ ε D → ∀ i : Fin N,
      HolderSeminormLE G (fun y => svec G (fun p => bgFieldC G a ν (bgC0 d L N) D p -
          approxField G a ν D.Ψ D.h p.1 p.2) y i) θ (2 - θ)
        (B / θ * ((lemma53Const d L + 3 / 2 * bgK1 d L N) * δ)) := by
  classical
  obtain ⟨B, hB0, hg⟩ := global_g2iv (d := d) (L := L) hd hL
  refine ⟨B, hB0, ?_⟩
  intro θ hθ0 hθ1 N k N₀ _ ϱ G a ν H D δ ε hδ0 hδε hε hδ hνε hDC i
  have hd0 : 0 < d := by omega
  obtain ⟨W⟩ := DataWit.exists hDC
  obtain ⟨φ, α, hs, hb, -, hu⟩ := bg_core H hδ0 hδε hε hδ hνε W
  obtain ⟨hf, -⟩ := bgFieldC_eq hs hu
  rw [hf]
  obtain ⟨hδa, -, hC32, -⟩ := bgC1_facts d L N hd0 hδ
  have hdelta := approxDelta_le d L hδa
  have S : ApproxSetting d L k ϱ a ν δ ε :=
    H.approxSetting hδ0 hδε (hε.trans (bgC0_le d L N)) hdelta.1 hνε
  obtain ⟨-, -, hres, -⟩ := lemma53 S hδa D W.real W (fun x hx i => W.real_Ψ hx i)
    (fun x hx i => W.real_h hx i)
  -- the perturbed system for the increment
  have hper := (isPerturbed_iff_isEL (a := a) (ν := ν) D (approxField G a ν D.Ψ D.h)
    (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2) α).2 (by
      convert hs.1 using 2; ring)
  set δφ : G.Ω 1 × Fin N → ℂ := fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2 with hδφ
  -- the source of the increment
  set f : G.Ω 1 → ℂ := fun x => residual G a ν D (approxField G a ν D.Ψ D.h) (x, i) -
    α x * approxField G a ν D.Ψ D.h x i with hfdef
  have hsm : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing (x : Torus d (N₀ * L ^ k))) ^ 2) := by
    intro x
    have h1 := hs.2 x
    have h2 : bgC0 d L N ≤ coerciveConst d / 8 := by
      have := (bgC0_le_c6 d L N)
      have h3 : c6 d L N ≤ gamma1 d / 4 := min_le_left _ _
      unfold gamma1 at h3
      linarith
    have hp : 0 < G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
      have := spacing_pos (G := G) (x := (x : Torus d (N₀ * L ^ k))); positivity
    have hcc := coerciveConst_pos hd0
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hCf0 : 0 ≤ (lemma53Const d L + 3 / 2 * bgK1 d L N) * δ := by
    have := lemma53Const_pos d L
    have := bgK1_pos d L N
    positivity
  have hfb : ∀ x : G.Ω 1, (G.spacing (x : Torus d (N₀ * L ^ k))) ^ 2 * ‖f x‖ ≤
      (lemma53Const d L + 3 / 2 * bgK1 d L N) * δ := by
    intro x
    have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
    have h1 : G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ‖residual G a ν D (approxField G a ν D.Ψ D.h) (x, i)‖ ≤ lemma53Const d L * δ :=
      (mul_le_mul_of_nonneg_left (norm_le_vn (fun j => residual G a ν D
        (approxField G a ν D.Ψ D.h) (x, j)) i) hp).trans (hres x)
    have hxd : (x : Torus d (N₀ * L ^ k)) ∈ dataSites G := (mem_dataSites G).2 (Or.inl x.2)
    have h2 : ‖approxField G a ν D.Ψ D.h x i‖ ≤ 3 / 2 :=
      (norm_le_vn _ i).trans (phi0_vn_lt S hδa W hC32 hxd).le
    have h3 := hb.alpha x
    have h4 : G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ‖α x * approxField G a ν D.Ψ D.h x i‖ ≤ 3 / 2 * (bgK1 d L N * δ) := by
      rw [norm_mul]
      calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (‖α x‖ * ‖approxField G a ν D.Ψ D.h x i‖)
          = (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x‖) *
              ‖approxField G a ν D.Ψ D.h x i‖ := by ring
        _ ≤ (bgK1 d L N * δ) * (3 / 2) :=
            mul_le_mul h3 h2 (norm_nonneg _) (le_trans (by positivity) h3)
        _ = 3 / 2 * (bgK1 d L N * δ) := by ring
    have := norm_sub_le (residual G a ν D (approxField G a ν D.Ψ D.h) (x, i))
      (α x * approxField G a ν D.Ψ D.h x i)
    have h5 := mul_le_mul_of_nonneg_left this hp
    show G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖f x‖ ≤ _
    simp only [hfdef]
    nlinarith
  -- the increment is the Green's function of `f`
  have hU : IsUnit (dirichletOperator G a ν α) :=
    dirichletOperator_isUnit G hd0 H.mass H.weights α hsm
  have hHf : dirichletOperator G a ν α *ᵥ (fun z : G.Ω 1 => δφ (z, i)) = f := by
    funext x
    have h1 := congrFun hper.1 (x, i)
    have h2 := liftOp_dirichlet_add (G := G) (N := N) a ν 0 α δφ (x, i)
    rw [zero_add] at h2
    have h3 := liftOp_mulVec (dirichletOperator G a ν α) δφ x i
    rw [← h3, h2]
    simp only [Pi.add_apply] at h1
    simp only [hfdef]
    linear_combination h1
  have hcomp : (fun z : G.Ω 1 => δφ (z, i)) = (dirichletOperator G a ν α)⁻¹ *ᵥ f := by
    rw [← hHf, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hU), Matrix.one_mulVec]
  have hgs : (fun y => svec G δφ y i) = greenSol G a ν α f := by
    funext y
    unfold greenSol svec
    rw [← hcomp]
  rw [show (fun y => svec G (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2) y i) =
    greenSol G a ν α f from hgs]
  exact (hg hθ0 hθ1 G H.mass H.massLe H.weights hsm (H.green (G := G)).sep f hCf0 hfb).2

end Balaban.Background
