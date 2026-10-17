/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomClose
public import Balaban.SmallField.RenormAnisoCtx
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Anisotropic data from the scaled source witness

This constructor exposes the geometric pullback, same-mass class chart, and second-difference
inputs. The sharp square estimate is the output of `xiC_scaledComposition_square_sharp`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale

variable {d L N₀ k N j : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {ν τ ζ σ ε K₂ : ℝ}
  {p : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h : Fin N → ℝ}
  {z h' : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- A scaled source datum pulled back through level sites satisfies `DataHypAniso`.
The two domain memberships are the same-mass chart inclusion; the second difference is
P1 (3.107). -/
theorem ScaledPsiC.dataHypAniso_of_pullback (H : ScaledPsiC G ν τ ζ j p h z h')
    (f : Site d → Torus d (N₀ * L ^ k)) (ψ : Site d → Spin N) (b : Spin N)
    (hψ : ∀ x i, ψ x i = (p (f x) i : ℂ) + z (f x) i)
    (hb : b = (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • fun i => (h i : ℂ) + h' (f 0) i))
    (hsite : ∀ x, f x ∈ G.Ω 1 ∧ G.layerIndex (f x) = j)
    (hadj : ∀ x μ, IsInterfacePair G (f (x + Pi.single μ 1)) (f x))
    (hsharp : ∀ x, ‖∑ i, ((p (f x) i : ℂ) + z (f x) i) *
          ((p (f x) i : ℂ) + z (f x) i) -
        ∑ i, (p (f x) i : ℂ) * (p (f x) i : ℂ)‖ < τ ^ 2 * ζ)
    (hν : 0 < ν * ((L : ℝ) ^ j) ^ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hντ : ν * ((L : ℝ) ^ j) ^ 2 ≤ τ ^ 2)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 200)
    (hsqNum : 2 * τ ^ 2 * ζ ≤ σ ^ 2 * ε)
    (hadjNum : 2 * τ * ζ ≤ σ * ε)
    (hcloseNum : 10 * τ ^ 2 * ζ ≤ σ ^ 2 * ε)
    (hlongNum : 98 * τ ^ 2 * ζ ^ 2 ≤ σ ^ 2 * ε ^ 2)
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (hchart : (ψ, b) ∈ Dom ∧ ((fun _ => ψ 0), b) ∈ Dom)
    (hK₂ : 0 ≤ K₂)
    (hsec : ∀ x μ μ', ‖ψ (x + Pi.single μ 1 + Pi.single μ' 1) -
      ψ (x + Pi.single μ 1) - ψ (x + Pi.single μ' 1) + ψ x‖ ≤ K₂) :
    DataHypAniso Dom (ν * ((L : ℝ) ^ j) ^ 2) σ ε K₂ ψ b := by
  let νj : ℝ := ν * ((L : ℝ) ^ j) ^ 2
  have hpi (v : Fin N → ℂ) : ‖v‖ ≤ vn v :=
    (pi_norm_le_iff_of_nonneg (vn_nonneg v)).2 fun i => norm_le_vn v i
  have hsquare : ∀ x, ‖dot (ψ x) (ψ x) - 1‖ ≤ σ ^ 2 * ε := by
    intro x
    have hsiteX := (hsite x).1
    have hp := H.r2 (f x) ((mem_dataSites G).2 (Or.inl hsiteX))
    have hc := hsharp x
    have he : dot (ψ x) (ψ x) - 1 =
        (∑ i, ((p (f x) i : ℂ) + z (f x) i) *
            ((p (f x) i : ℂ) + z (f x) i) -
          ∑ i, (p (f x) i : ℂ) * (p (f x) i : ℂ)) +
        ((∑ i, p (f x) i ^ 2 - 1 : ℝ) : ℂ) := by
      simp only [dot, hψ]
      push_cast
      simp only [sq]
      ring
    have htri : ‖dot (ψ x) (ψ x) - 1‖ ≤
        ‖∑ i, ((p (f x) i : ℂ) + z (f x) i) *
            ((p (f x) i : ℂ) + z (f x) i) -
          ∑ i, (p (f x) i : ℂ) * (p (f x) i : ℂ)‖ +
          |∑ i, p (f x) i ^ 2 - 1| := by
      calc
        _ = ‖(∑ i, ((p (f x) i : ℂ) + z (f x) i) *
            ((p (f x) i : ℂ) + z (f x) i) -
          ∑ i, (p (f x) i : ℂ) * (p (f x) i : ℂ)) +
          ((∑ i, p (f x) i ^ 2 - 1 : ℝ) : ℂ)‖ := congrArg norm he
        _ ≤ ‖∑ i, ((p (f x) i : ℂ) + z (f x) i) *
            ((p (f x) i : ℂ) + z (f x) i) -
          ∑ i, (p (f x) i : ℂ) * (p (f x) i : ℂ)‖ +
          ‖((∑ i, p (f x) i ^ 2 - 1 : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ ‖∑ i, ((p (f x) i : ℂ) + z (f x) i) *
            ((p (f x) i : ℂ) + z (f x) i) -
          ∑ i, (p (f x) i : ℂ) * (p (f x) i : ℂ)‖ +
          |∑ i, p (f x) i ^ 2 - 1| := htri
      _ ≤ 2 * τ ^ 2 * ζ := by linarith
      _ ≤ σ ^ 2 * ε := hsqNum
  have hadjBound : ∀ x μ, ‖ψ (x + Pi.single μ 1) - ψ x‖ ≤ σ * ε := by
    intro x μ
    let x' := x + Pi.single μ 1
    have hp := H.r1 (f x') (f x) (hadj x μ)
    have hz := H.c1 (f x') (f x) (hadj x μ)
    have he : ψ x' - ψ x =
        (fun i => (((p (f x') i - p (f x) i : ℝ) : ℂ))) +
          (z (f x') - z (f x)) := by
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, hψ]
      push_cast
      ring
    rw [he]
    have hreal : vn (fun i => ((p (f x') i - p (f x) i : ℝ) : ℂ)) < τ * ζ := by
      rwa [vn_ofReal]
    calc
      _ ≤ vn ((fun i => ((p (f x') i - p (f x) i : ℝ) : ℂ)) +
          (z (f x') - z (f x))) := hpi _
      _ ≤ vn (fun i => ((p (f x') i - p (f x) i : ℝ) : ℂ)) +
          vn (z (f x') - z (f x)) := vn_add' _ _
      _ ≤ 2 * τ * ζ := by linarith
      _ ≤ σ * ε := hadjNum
  have hbdd : ‖ψ 0‖ ≤ 2 := by
    have hsite0 := (hsite 0).1
    have hp := H.r2 (f 0) ((mem_dataSites G).2 (Or.inl hsite0))
    have hz := H.c2a (f 0) ((mem_dataSites G).2 (Or.inl hsite0))
    have hρ := abs_rn_sub_one_le (p (f 0))
    have hρle : rn (p (f 0)) ≤ 1 + τ ^ 2 * ζ := by
      have := le_abs_self (rn (p (f 0)) - 1)
      linarith [hρ]
    have he : ψ 0 = (fun i => (p (f 0) i : ℂ)) + z (f 0) := by
      funext i; exact hψ 0 i
    rw [he]
    have hτ2 : τ ^ 2 ≤ 1 := by nlinarith
    calc
      _ ≤ vn ((fun i => (p (f 0) i : ℂ)) + z (f 0)) := hpi _
      _ ≤ rn (p (f 0)) + vn (z (f 0)) := by
        change vn (fun i => (p (f 0) i : ℂ) + z (f 0) i) ≤ _
        simpa only [vn_ofReal] using vn_add' (fun i => (p (f 0) i : ℂ)) (z (f 0))
      _ ≤ 2 := by nlinarith [hζ1, hτ2]
  have hclose : ‖b - (νj : ℂ) • ψ 0‖ ≤ σ ^ 2 * ε := by
    have hh := ScaledPsiC.b_close H (hsite 0).1 (hsite 0).2 hν hτ hτ1 hντ hζ hζ1
    have he : ψ 0 = fun i => (p (f 0) i : ℂ) + z (f 0) i := by
      funext i; exact hψ 0 i
    rw [hb, he]
    exact hh.trans hcloseNum
  have hlong : ‖vInv ψ b - νj‖ ≤ σ ^ 2 * ε ^ 2 := by
    have hh := ScaledPsiC.vInv_bound_of_square_sharp H (hsite 0).1 (hsite 0).2
      hν hτ hτ1 hντ hζ hζ1 (hsharp 0)
    have he : ψ 0 = fun i => (p (f 0) i : ℂ) + z (f 0) i := by
      funext i; exact hψ 0 i
    rw [hb]
    change ‖dot (ψ 0) _ / sqrtC (dot (ψ 0) (ψ 0)) - νj‖ ≤ _
    rw [he]
    exact hh.trans hlongNum
  exact ⟨⟨hK₂, hsquare, hbdd, hadjBound, hclose, hsec, hchart.1, hchart.2⟩, hlong⟩

end Balaban.SmallField
