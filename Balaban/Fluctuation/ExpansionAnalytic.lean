module

public import Balaban.Fluctuation.ExpansionLocal
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Lemma 2.3 (d): analyticity of the interaction

`interactionBlock_analyticAt`: the block interaction `V^{(k)}(z)` is a polynomial in the
coordinates of `(ψ', φ')`, hence analytic when these depend analytically on a parameter.
`interactionBlock_analytic`: composing with the analytic function of the data of
`theorem72_analytic`, `ψ' ↦ V^{(k)}(z; ψ')` is the restriction of a function analytic on the set of
tangents for which the datum stays in the domain `𝒟` (P4 (2.29)).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Finset Matrix

section Analytic

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'} {a : ℕ → ℝ} {ν : ℝ} {m : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A vector-valued function of a parameter is *coordinatewise analytic* at `ξ₀`. -/
def CoordAn {ι : Type*} (w : E → ι → ℂ) (ξ₀ : E) : Prop :=
  ∀ q, AnalyticAt ℂ (fun ξ => w ξ q) ξ₀

theorem CoordAn.mulVec {ι κ : Type*} [Fintype ι] {w : E → ι → ℂ} {ξ₀ : E} (hw : CoordAn w ξ₀)
    (M : Matrix κ ι ℂ) : CoordAn (fun ξ => M *ᵥ w ξ) ξ₀ := by
  intro q
  simp only [Matrix.mulVec, dotProduct]
  have := hw
  unfold CoordAn at this
  fun_prop

theorem CoordAn.sub {ι : Type*} {w v : E → ι → ℂ} {ξ₀ : E} (hw : CoordAn w ξ₀) (hv : CoordAn v ξ₀) :
    CoordAn (fun ξ => w ξ - v ξ) ξ₀ := fun q => (hw q).sub (hv q)

theorem CoordAn.const {ι : Type*} (c : ι → ℂ) (ξ₀ : E) : CoordAn (fun _ : E => c) ξ₀ :=
  fun _ => analyticAt_const

/-- `interactionBlock` is analytic in the parameters `(ψ', φ')` that depend coordinatewise
analytically on `ξ`: it is a polynomial in their coordinates. -/
theorem interactionBlock_analyticAt (hG : IsLevel G m) (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ)
    (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ) (j : ℕ) (z : Torus d (N₀ * L ^ (K - j)))
    {ψ : E → Torus d (N₀ * L ^ K) → Fin N → ℂ} {φ' : E → G.Ω 1 × Fin N → ℂ} {ξ₀ : E}
    (hψ : ∀ y i, AnalyticAt ℂ (fun ξ => ψ ξ y i) ξ₀) (hφ : CoordAn φ' ξ₀) :
    AnalyticAt ℂ (fun ξ => interactionBlock h a ν α₁ φ₁ (ψ ξ) (φ' ξ) j z) ξ₀ := by
  classical
  have hS : CoordAn (fun ξ => qStar G a (ψ ξ)) ξ₀ := fun q => by
    show AnalyticAt ℂ (fun ξ => ((a (G.layerIndex (q.1 : Torus d (N₀ * L ^ K))) /
      ((L : ℝ) ^ G.layerIndex (q.1 : Torus d (N₀ * L ^ K))) ^ 2 : ℝ) : ℂ) * ψ ξ q.1 q.2) ξ₀
    exact analyticAt_const.mul (hψ _ _)
  have hP : CoordAn (fun ξ => phiOne h a ν α₁ φ₁ (qStar G a (ψ ξ))) ξ₀ := hS.mulVec _
  have hA : CoordAn (fun ξ => alphaOne h a ν α₁ φ₁ (qStar G a (ψ ξ))) ξ₀ :=
    ((hS.mulVec _).mulVec _).mulVec _
  have hU : CoordAn (fun ξ => φ' ξ - phiOne h a ν α₁ φ₁ (qStar G a (ψ ξ))) ξ₀ := hφ.sub hP
  have hHU : CoordAn (fun ξ => liftOp N (opHk h a ν α₁) *ᵥ
      (φ' ξ - phiOne h a ν α₁ φ₁ (qStar G a (ψ ξ)))) ξ₀ := hU.mulVec _
  unfold interactionBlock
  refine Finset.analyticAt_fun_sum _ fun x _ => ?_
  have hx : x ∈ G.Ω 1 := (hG x).1
  unfold interactionDensity
  simp only [svec_eq_apply hG, zeroExt, hx, dite_true]
  have h1 := hφ
  have h2 := hA
  have h3 := hU
  have h4 := hHU
  unfold CoordAn at h1 h2 h3 h4
  fun_prop

/-- **Analyticity of the interaction** (Lemma 2.3 (d)): for a base datum `B`, the block interaction
`V^{(k)}(z; ψ')`, as a function of the tangent `ψ' = D.Ψ - B.Ψ`, is the restriction of a function
analytic on the set of tangents for which the datum `D` (with the same `h̃`) stays in the domain `𝒟`
(composition of the analytic function of the data of `theorem72_analytic` with a polynomial). -/
theorem interactionBlock_analytic (hG : IsLevel G m) (H : BgHyp d L K ϱ a ν) (B : BgData G N)
    (h : Precedes G G') (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ) (j : ℕ)
    (z : Torus d (N₀ * L ^ (K - j))) :
    ∃ Vz : (Torus d (N₀ * L ^ K) → Fin N → ℂ) → ℂ,
      AnalyticOnNhd ℂ Vz {ξ | ∃ D : BgData G N,
        InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D ∧ D.h = B.h ∧
          ξ = fun x i => D.Ψ x i - B.Ψ x i} ∧
      ∀ D : BgData G N, InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D → D.h = B.h →
        Vz (fun x i => D.Ψ x i - B.Ψ x i) = interactionBlock h a ν α₁ φ₁
          (fun x i => D.Ψ x i - B.Ψ x i)
          (bgFieldC G a ν (bgC0 d L N) D - h.restrictφ φ₁) j z := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := G) (a := a) (ν := ν) H
  refine ⟨fun ξ => interactionBlock h a ν α₁ φ₁ ξ
    ((F (B.Ψ + ξ, B.h)).1 - h.restrictφ φ₁) j z, ?_, ?_⟩
  · rintro ξ₀ ⟨D, hD, hh, rfl⟩
    have hmem : (B.Ψ + (fun x i => D.Ψ x i - B.Ψ x i), B.h) ∈ {p : RawData d L N₀ K N | ∃ D : BgData G N,
        InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)} :=
      ⟨D, hD, Prod.ext (by funext x i; simp) hh.symm⟩
    have hγ : AnalyticAt ℂ (fun ξ : Torus d (N₀ * L ^ K) → Fin N → ℂ =>
        ((B.Ψ + ξ, B.h) : RawData d L N₀ K N)) (fun x i => D.Ψ x i - B.Ψ x i) :=
      (analyticAt_const.add analyticAt_id).prod analyticAt_const
    have hFa : AnalyticAt ℂ (fun ξ : Torus d (N₀ * L ^ K) → Fin N → ℂ => F (B.Ψ + ξ, B.h))
        (fun x i => D.Ψ x i - B.Ψ x i) :=
      AnalyticAt.comp (f := fun ξ : Torus d (N₀ * L ^ K) → Fin N → ℂ => ((B.Ψ + ξ, B.h) : RawData d L N₀ K N)) (hF _ hmem) hγ
    refine interactionBlock_analyticAt hG h a ν α₁ φ₁ j z (ψ := fun ξ => ξ)
      (φ' := fun ξ => (F (B.Ψ + ξ, B.h)).1 - h.restrictφ φ₁) (fun y i => ?_) (fun q => ?_)
    · have hy : AnalyticAt ℂ (fun ξ : Torus d (N₀ * L ^ K) → Fin N → ℂ => ξ y)
          (fun x i => D.Ψ x i - B.Ψ x i) := analyticAt_pi_iff.1 analyticAt_id y
      exact analyticAt_pi_iff.1 hy i
    · have h1 : AnalyticAt ℂ (fun ξ : Torus d (N₀ * L ^ K) → Fin N → ℂ =>
          (F (B.Ψ + ξ, B.h)).1) (fun x i => D.Ψ x i - B.Ψ x i) := analyticAt_fst.comp hFa
      exact (analyticAt_pi_iff.1 h1 q).sub analyticAt_const
  · intro D hD hh
    have hp : (B.Ψ + fun x i => D.Ψ x i - B.Ψ x i, B.h) = (D.Ψ, D.h) :=
      Prod.ext (by funext x i; simp) hh.symm
    simp only [hp, hFe D hD]

end Analytic

end Balaban.Fluctuation
