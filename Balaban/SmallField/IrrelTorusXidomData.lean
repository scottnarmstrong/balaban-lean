/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomClose
public import Balaban.SmallField.RenormAnisoCtx
public import Balaban.SmallField.RenormAnisoPath
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

/-- (Σ1) at a pulled-back site of `Ω₁` (with the sharp square estimate there). -/
theorem ScaledPsiC.sq_of_pullback_at (H : ScaledPsiC G ν τ ζ j p h z h')
    (f : Site d → Torus d (N₀ * L ^ k)) (ψ : Site d → Spin N)
    (hψ : ∀ x i, ψ x i = (p (f x) i : ℂ) + z (f x) i) {x : Site d}
    (hsiteX : f x ∈ G.Ω 1)
    (hsharp : ‖∑ i, ((p (f x) i : ℂ) + z (f x) i) *
          ((p (f x) i : ℂ) + z (f x) i) -
        ∑ i, (p (f x) i : ℂ) * (p (f x) i : ℂ)‖ < τ ^ 2 * ζ)
    (hsqNum : 2 * τ ^ 2 * ζ ≤ σ ^ 2 * ε) :
    ‖dot (ψ x) (ψ x) - 1‖ ≤ σ ^ 2 * ε := by
  have hp := H.r2 (f x) ((mem_dataSites G).2 (Or.inl hsiteX))
  have hc := hsharp
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

/-- The first difference across an interface pair of pulled-back sites. -/
theorem ScaledPsiC.adj_of_pullback_at (H : ScaledPsiC G ν τ ζ j p h z h')
    (f : Site d → Torus d (N₀ * L ^ k)) (ψ : Site d → Spin N)
    (hψ : ∀ x i, ψ x i = (p (f x) i : ℂ) + z (f x) i) {x : Site d} {μ : Fin d}
    (hadj : IsInterfacePair G (f (x + Pi.single μ 1)) (f x))
    (hadjNum : 2 * τ * ζ ≤ σ * ε) :
    ‖ψ (x + Pi.single μ 1) - ψ x‖ ≤ σ * ε := by
  have hpi (v : Fin N → ℂ) : ‖v‖ ≤ vn v :=
    (pi_norm_le_iff_of_nonneg (vn_nonneg v)).2 fun i => norm_le_vn v i
  let x' := x + Pi.single μ 1
  have hp := H.r1 (f x') (f x) hadj
  have hz := H.c1 (f x') (f x) hadj
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

/-- The bound `‖ψ(0)‖ ≤ 2` at a pulled-back site of `Ω₁`. -/
theorem ScaledPsiC.bdd0_of_pullback (H : ScaledPsiC G ν τ ζ j p h z h')
    (f : Site d → Torus d (N₀ * L ^ k)) (ψ : Site d → Spin N)
    (hψ : ∀ x i, ψ x i = (p (f x) i : ℂ) + z (f x) i)
    (hsite0 : f 0 ∈ G.Ω 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 200) :
    ‖ψ 0‖ ≤ 2 := by
  have hpi (v : Fin N → ℂ) : ‖v‖ ≤ vn v :=
    (pi_norm_le_iff_of_nonneg (vn_nonneg v)).2 fun i => norm_le_vn v i
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

/-- The closeness `‖b - ν_j ψ(0)‖ ≤ σ² ε` at a pulled-back site of the layer `j`. -/
theorem ScaledPsiC.b_close_of_pullback (H : ScaledPsiC G ν τ ζ j p h z h')
    (f : Site d → Torus d (N₀ * L ^ k)) (ψ : Site d → Spin N) (b : Spin N)
    (hψ : ∀ x i, ψ x i = (p (f x) i : ℂ) + z (f x) i)
    (hb : b = (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • fun i => (h i : ℂ) + h' (f 0) i))
    (hsite0 : f 0 ∈ G.Ω 1 ∧ G.layerIndex (f 0) = j)
    (hν : 0 < ν * ((L : ℝ) ^ j) ^ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hντ : ν * ((L : ℝ) ^ j) ^ 2 ≤ τ ^ 2)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 200)
    (hcloseNum : 10 * τ ^ 2 * ζ ≤ σ ^ 2 * ε) :
    ‖b - (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ)) • ψ 0‖ ≤ σ ^ 2 * ε := by
  have hh := ScaledPsiC.b_close H hsite0.1 hsite0.2 hν hτ hτ1 hντ hζ hζ1
  have he : ψ 0 = fun i => (p (f 0) i : ℂ) + z (f 0) i := by
    funext i; exact hψ 0 i
  rw [hb, he]
  exact hh.trans hcloseNum

/-- The longitudinal bound at a pulled-back site of the layer `j`. -/
theorem ScaledPsiC.b_long_of_pullback (H : ScaledPsiC G ν τ ζ j p h z h')
    (f : Site d → Torus d (N₀ * L ^ k)) (ψ : Site d → Spin N) (b : Spin N)
    (hψ : ∀ x i, ψ x i = (p (f x) i : ℂ) + z (f x) i)
    (hb : b = (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • fun i => (h i : ℂ) + h' (f 0) i))
    (hsite0 : f 0 ∈ G.Ω 1 ∧ G.layerIndex (f 0) = j)
    (hsharp0 : ‖∑ i, ((p (f 0) i : ℂ) + z (f 0) i) *
          ((p (f 0) i : ℂ) + z (f 0) i) -
        ∑ i, (p (f 0) i : ℂ) * (p (f 0) i : ℂ)‖ < τ ^ 2 * ζ)
    (hν : 0 < ν * ((L : ℝ) ^ j) ^ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hντ : ν * ((L : ℝ) ^ j) ^ 2 ≤ τ ^ 2)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 200)
    (hlongNum : 98 * τ ^ 2 * ζ ^ 2 ≤ σ ^ 2 * ε ^ 2) :
    ‖vInv ψ b - (ν * ((L : ℝ) ^ j) ^ 2 : ℝ)‖ ≤ σ ^ 2 * ε ^ 2 := by
  have hh := ScaledPsiC.vInv_bound_of_square_sharp H hsite0.1 hsite0.2
    hν hτ hτ1 hντ hζ hζ1 hsharp0
  have he : ψ 0 = fun i => (p (f 0) i : ℂ) + z (f 0) i := by
    funext i; exact hψ 0 i
  rw [hb]
  change ‖dot (ψ 0) _ / sqrtC (dot (ψ 0) (ψ 0)) - (ν * ((L : ℝ) ^ j) ^ 2 : ℝ)‖ ≤ _
  rw [he]
  exact hh.trans hlongNum

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
  exact ⟨⟨hK₂, fun x => ScaledPsiC.sq_of_pullback_at H f ψ hψ (hsite x).1 (hsharp x) hsqNum,
    ScaledPsiC.bdd0_of_pullback H f ψ hψ (hsite 0).1 hτ hτ1 hζ hζ1,
    fun x μ => ScaledPsiC.adj_of_pullback_at H f ψ hψ (hadj x μ) hadjNum,
    ScaledPsiC.b_close_of_pullback H f ψ b hψ hb (hsite 0) hν hτ hτ1 hντ hζ hζ1 hcloseNum, hsec,
    hchart.1, hchart.2⟩,
    ScaledPsiC.b_long_of_pullback H f ψ b hψ hb (hsite 0) (hsharp 0) hν hτ hτ1 hντ hζ hζ1 hlongNum⟩

/-- **A scaled source datum pulled back through the sites of a region `R` gives the data on the
polymers** (the local form of `ScaledPsiC.dataHypAniso_of_pullback`, through
`DataHypAnisoOn.of_paths`): the pulled-back sites of `R` lie in `Ω₁` and in the layer `j` (at the
origin) of `G`, the edges of `R` are interface pairs, the sharp square estimate on `R`, the second
differences of the plaquettes of `R`, the origin with its forward star in `R`, and for every site
of a polymer a path from the origin of at most `ℓ X` steps inside `R` with the forward stars. -/
theorem ScaledPsiC.dataHypAnisoOn_of_pullback (H : ScaledPsiC G ν τ ζ j p h z h')
    (f : Site d → Torus d (N₀ * L ^ k)) (ψ : Site d → Spin N) (b : Spin N)
    (hψ : ∀ x i, ψ x i = (p (f x) i : ℂ) + z (f x) i)
    (hb : b = (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • fun i => (h i : ℂ) + h' (f 0) i))
    {R : Set (Site d)}
    (hsite : ∀ x ∈ R, f x ∈ G.Ω 1) (hsite0 : G.layerIndex (f 0) = j)
    (hadj : ∀ x μ, x ∈ R → x + eU μ ∈ R → IsInterfacePair G (f (x + Pi.single μ 1)) (f x))
    (hsharp : ∀ x ∈ R, ‖∑ i, ((p (f x) i : ℂ) + z (f x) i) *
          ((p (f x) i : ℂ) + z (f x) i) -
        ∑ i, (p (f x) i : ℂ) * (p (f x) i : ℂ)‖ < τ ^ 2 * ζ)
    (hν : 0 < ν * ((L : ℝ) ^ j) ^ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hντ : ν * ((L : ℝ) ^ j) ^ 2 ≤ τ ^ 2)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 200)
    (hsqNum : 2 * τ ^ 2 * ζ ≤ σ ^ 2 * ε)
    (hadjNum : 2 * τ * ζ ≤ σ * ε)
    (hcloseNum : 10 * τ ^ 2 * ζ ≤ σ ^ 2 * ε)
    (hlongNum : 98 * τ ^ 2 * ζ ^ 2 ≤ σ ^ 2 * ε ^ 2)
    {polys : Set (Finset (Site d))} {ℓ : Finset (Site d) → ℝ} (h0 : StarIn R 0)
    (hpath : ∀ X ∈ polys, ∀ x ∈ X, ∃ (q : ℕ → Site d) (n : ℕ), q 0 = 0 ∧ q n = x ∧
      (n : ℝ) ≤ ℓ X ∧ IsLatPath q n ∧ ∀ i ≤ n, StarIn R (q i))
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (hchart : (ψ, b) ∈ Dom ∧ ((fun _ => ψ 0), b) ∈ Dom)
    (hK₂ : 0 ≤ K₂)
    (hsec : ∀ x μ μ', x ∈ R → x + eU μ ∈ R → x + eU μ' ∈ R → x + eU μ + eU μ' ∈ R →
      ‖ψ (x + Pi.single μ 1 + Pi.single μ' 1) - ψ (x + Pi.single μ 1) -
        ψ (x + Pi.single μ' 1) + ψ x‖ ≤ K₂) :
    DataHypAnisoOn polys ℓ Dom (ν * ((L : ℝ) ^ j) ^ 2) σ ε K₂ ψ b := by
  have hσε : 0 ≤ σ * ε := le_trans (by positivity) hadjNum
  have hs0 : f 0 ∈ G.Ω 1 ∧ G.layerIndex (f 0) = j := ⟨hsite 0 h0.1, hsite0⟩
  refine DataHypAnisoOn.of_paths hK₂ (fun x μ hx hxμ => ?_) hsec
    (fun x hx => ScaledPsiC.sq_of_pullback_at H f ψ hψ (hsite x hx) (hsharp x hx) hsqNum) h0 hσε hpath
    (ScaledPsiC.bdd0_of_pullback H f ψ hψ hs0.1 hτ hτ1 hζ hζ1)
    (ScaledPsiC.b_close_of_pullback H f ψ b hψ hb hs0 hν hτ hτ1 hντ hζ hζ1 hcloseNum)
    (ScaledPsiC.b_long_of_pullback H f ψ b hψ hb hs0 (hsharp 0 h0.1) hν hτ hτ1 hντ hζ hζ1 hlongNum)
    hchart.1 hchart.2
  simpa [eU] using ScaledPsiC.adj_of_pullback_at H f ψ hψ (hadj x μ hx hxμ) hadjNum

end Balaban.SmallField
