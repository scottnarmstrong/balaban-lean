/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRJac
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRTerms`: the partition function as the expectation of a product of local terms (route FR,
(R4)–(R5))

`notes/phase1/KF0-FR.md` (R4), (R5). The site variables are `ω_x = (ψ_x, σ_x) ∈ h^⊥ × Bool`, with
the reference measure `γ ⊗ π_ε` at each site: `γ` the standard Gaussian of `h^⊥` and `π_ε` the
Bernoulli law of the sheets, `π_ε(true) = 1/(1+ε)`, `π_ε(false) = ε/(1+ε)` (`frBern`). The factor
`b(false) = ε^{-1}` (`bW`) compensates the Bernoulli law. With `u = β^{-1/2} C_R ψ`, `t = √(1-|u|²)`,
`s = ±1` the signs of the sheets and `Φ_x = u_x + s_x t_x h` the spin, the terms are

* the site term (`frSite`): `w(u_x) b(σ_x) e^{-(βν/2)(s_x t_x - 1)²} e^{⟨g_x, Φ_x - h⟩}
  e^{-½ ∑_y Q_R(x,y) ⟨ψ_x, ψ_y⟩}`;
* the bond term (`frBond`): `e^{-(β/2)(s_y t_y - s_x t_x)²}`, `y = x + e_μ`.

`partitionFunction_eq_terms`: `Z(g) = c (1+ε)^{|Λ|} e^{⟨g,h⟩} ∫ ∏_t F_t dμ`, `μ = ⊗_x (γ ⊗ π_ε)`, for
every complex source, when the defect of the whitening has row sums at most `1`.
-/

@[expose] public section

open MeasureTheory Set Matrix Balaban.Green
open scoped ENNReal

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

local notation "E" => EuclideanSpace ℝ (Fin N)
local notation "Sph" => Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

/-! ### The site measure -/

/-- The Bernoulli law of the sheets: `true` with probability `1/(1+ε)`, `false` with `ε/(1+ε)`. -/
def frBern (ε : ℝ) : Measure Bool :=
  ENNReal.ofReal (1 / (1 + ε)) • Measure.dirac true + ENNReal.ofReal (ε / (1 + ε)) • Measure.dirac false

theorem frBern_true {ε : ℝ} : (frBern ε) {true} = ENNReal.ofReal (1 / (1 + ε)) := by
  simp [frBern]

theorem frBern_false {ε : ℝ} : (frBern ε) {false} = ENNReal.ofReal (ε / (1 + ε)) := by
  simp [frBern]

theorem frBern_univ {ε : ℝ} (hε : 0 ≤ ε) : (frBern ε) Set.univ = 1 := by
  simp only [frBern, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [show 1 / (1 + ε) + ε / (1 + ε) = 1 by field_simp]
  simp

theorem isProbabilityMeasure_frBern {ε : ℝ} (hε : 0 ≤ ε) : IsProbabilityMeasure (frBern ε) :=
  ⟨frBern_univ hε⟩

/-- The site measure `γ ⊗ π_ε`. -/
def frSiteMeasure (ε : ℝ) : Measure (perp h × Bool) := (oneSiteGaussian (perp h)).prod (frBern ε)

theorem isProbabilityMeasure_frSiteMeasure {ε : ℝ} (hε : 0 ≤ ε) :
    IsProbabilityMeasure (frSiteMeasure h ε) := by
  have := isProbabilityMeasure_frBern hε
  unfold frSiteMeasure; infer_instance

/-- The weight compensating the Bernoulli law. -/
def bW (ε : ℝ) (b : Bool) : ℝ := if b then 1 else ε⁻¹

variable {d ℓ : ℕ} [NeZero ℓ]

/-- The Gaussian variables of a site configuration. -/
def frPsi (ω : Torus d ℓ → perp h × Bool) : Torus d ℓ → perp h := fun x => (ω x).1

/-- The sheets of a site configuration. -/
def frSig (ω : Torus d ℓ → perp h × Bool) : Torus d ℓ → Bool := fun x => (ω x).2

/-! ### The terms -/

/-- The terms: one for each site, one for each bond. -/
abbrev FRTerm (d ℓ : ℕ) := Torus d ℓ ⊕ (Torus d ℓ × Fin d)

/-- **The site term** at `x`. -/
def frSite (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d ℓ → Fin N → ℂ) (x : Torus d ℓ)
    (ω : Torus d ℓ → perp h × Bool) : ℂ :=
  ((chartWeight h (frField d ℓ β ν R (frPsi h ω) x) * bW ε (frSig h ω x) *
      Real.exp (-(β * ν / 2) * (sgn (frSig h ω x) * tN h (frField d ℓ β ν R (frPsi h ω) x) - 1) ^ 2)
      : ℝ) : ℂ) *
    Complex.exp (∑ i : Fin N, g x i *
      ((((sheetPt h hh (frSig h ω x) (frField d ℓ β ν R (frPsi h ω) x) : Sph) : E) - h) i : ℂ)) *
    ((Real.exp (-(1 / 2) * ∑ y, frQ d ℓ ν R x y *
      inner ℝ (frPsi h ω x : E) (frPsi h ω y : E)) : ℝ) : ℂ)

/-- **The bond term** of the bond `(x, x + e_μ)`. -/
def frBond (β ν : ℝ) (R : ℕ) (x : Torus d ℓ) (μ : Fin d) (ω : Torus d ℓ → perp h × Bool) : ℂ :=
  ((Real.exp (-(β / 2) *
    (sgn (frSig h ω (x + Pi.single μ 1)) * tN h (frField d ℓ β ν R (frPsi h ω) (x + Pi.single μ 1))
      - sgn (frSig h ω x) * tN h (frField d ℓ β ν R (frPsi h ω) x)) ^ 2) : ℝ) : ℂ)

/-- The terms. -/
def frF (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d ℓ → Fin N → ℂ) :
    FRTerm d ℓ → (Torus d ℓ → perp h × Bool) → ℂ
  | Sum.inl x => frSite h hh β ν ε R g x
  | Sum.inr (x, μ) => frBond h β ν R x μ

/-- The exponent of a site term. -/
def frSiteExp (hh : ‖h‖ = 1) (β ν : ℝ) (R : ℕ) (g : Torus d ℓ → Fin N → ℂ) (x : Torus d ℓ)
    (ω : Torus d ℓ → perp h × Bool) : ℂ :=
  ((-(β * ν / 2) * (sgn (frSig h ω x) * tN h (frField d ℓ β ν R (frPsi h ω) x) - 1) ^ 2 : ℝ) : ℂ) +
    ∑ i : Fin N, g x i *
      ((((sheetPt h hh (frSig h ω x) (frField d ℓ β ν R (frPsi h ω) x) : Sph) : E) - h) i : ℂ) +
    ((-(1 / 2) * ∑ y, frQ d ℓ ν R x y *
      inner ℝ (frPsi h ω x : E) (frPsi h ω y : E) : ℝ) : ℂ)

theorem frSite_eq (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d ℓ → Fin N → ℂ) (x : Torus d ℓ)
    (ω : Torus d ℓ → perp h × Bool) :
    frSite h hh β ν ε R g x ω =
      ((chartWeight h (frField d ℓ β ν R (frPsi h ω) x) * bW ε (frSig h ω x) : ℝ) : ℂ) *
        Complex.exp (frSiteExp h hh β ν R g x ω) := by
  unfold frSite frSiteExp
  rw [Complex.exp_add, Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_exp]
  ring

/-- The exponent of a bond term. -/
def frBondExp (β ν : ℝ) (R : ℕ) (x : Torus d ℓ) (μ : Fin d) (ω : Torus d ℓ → perp h × Bool) : ℝ :=
  -(β / 2) *
    (sgn (frSig h ω (x + Pi.single μ 1)) * tN h (frField d ℓ β ν R (frPsi h ω) (x + Pi.single μ 1))
      - sgn (frSig h ω x) * tN h (frField d ℓ β ν R (frPsi h ω) x)) ^ 2

theorem neg_mul_frV (β ν : ℝ) (σ : Torus d ℓ → Bool) (ξ : Torus d ℓ → perp h) :
    -(β * frV h ν σ ξ) =
      ∑ x : Torus d ℓ, ∑ μ : Fin d, -(β / 2) *
          (sgn (σ (x + Pi.single μ 1)) * tN h (ξ (x + Pi.single μ 1)) - sgn (σ x) * tN h (ξ x)) ^ 2
        + ∑ x : Torus d ℓ, -(β * ν / 2) * (sgn (σ x) * tN h (ξ x) - 1) ^ 2 := by
  unfold frV
  rw [show -(β * ((1 / 2) * ∑ x : Torus d ℓ, ∑ μ : Fin d,
      (sgn (σ (x + Pi.single μ 1)) * tN h (ξ (x + Pi.single μ 1)) - sgn (σ x) * tN h (ξ x)) ^ 2
      + (ν / 2) * ∑ x : Torus d ℓ, (sgn (σ x) * tN h (ξ x) - 1) ^ 2)) =
      -(β / 2) * ∑ x : Torus d ℓ, ∑ μ : Fin d,
        (sgn (σ (x + Pi.single μ 1)) * tN h (ξ (x + Pi.single μ 1)) - sgn (σ x) * tN h (ξ x)) ^ 2
      + -(β * ν / 2) * ∑ x : Torus d ℓ, (sgn (σ x) * tN h (ξ x) - 1) ^ 2 by ring]
  simp only [Finset.mul_sum]

/-- **The factorization (R5)**: the whitened chart integrand times the Bernoulli weights is
`e^{⟨g,h⟩}` times the product of the terms. -/
theorem prod_frF_eq (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d ℓ → Fin N → ℂ)
    (ω : Torus d ℓ → perp h × Bool) :
    ((Real.exp (-(1 / 2) * ∑ x, ∑ y, frQ d ℓ ν R x y *
        inner ℝ (frPsi h ω x : E) (frPsi h ω y : E)) : ℝ) : ℂ) *
      frA h hh β ν (frSig h ω) g (frField d ℓ β ν R (frPsi h ω)) *
      ((∏ x, bW ε (frSig h ω x) : ℝ) : ℂ) =
    Complex.exp (∑ x : Torus d ℓ, ∑ i : Fin N, g x i * (h i : ℂ)) *
      ∏ t : FRTerm d ℓ, frF h hh β ν ε R g t ω := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  set W : ℂ := ∏ x, ((chartWeight h (frField d ℓ β ν R (frPsi h ω) x) : ℝ) : ℂ) with hW
  set Bw : ℂ := ∏ x, ((bW ε (frSig h ω x) : ℝ) : ℂ) with hBw
  have hsite : ∏ x, frF h hh β ν ε R g (Sum.inl x) ω =
      W * Bw * Complex.exp (∑ x, frSiteExp h hh β ν R g x ω) := by
    simp only [frF, frSite_eq, Finset.prod_mul_distrib, Complex.exp_sum, Complex.ofReal_mul, hW, hBw]
  have hbond : ∏ x, ∏ μ, frF h hh β ν ε R g (Sum.inr (x, μ)) ω =
      Complex.exp (∑ x, ∑ μ, ((frBondExp h β ν R x μ ω : ℝ) : ℂ)) := by
    simp only [frF, frBond, Complex.exp_sum, Complex.ofReal_exp]
    rfl
  rw [hsite, hbond]
  have hL : ((Real.exp (-(1 / 2) * ∑ x, ∑ y, frQ d ℓ ν R x y *
        inner ℝ (frPsi h ω x : E) (frPsi h ω y : E)) : ℝ) : ℂ) *
      frA h hh β ν (frSig h ω) g (frField d ℓ β ν R (frPsi h ω)) *
      ((∏ x, bW ε (frSig h ω x) : ℝ) : ℂ) =
      W * Bw * Complex.exp ((((-(1 / 2) * ∑ x, ∑ y, frQ d ℓ ν R x y *
        inner ℝ (frPsi h ω x : E) (frPsi h ω y : E)) : ℝ) : ℂ) +
        (((-(β * frV h ν (frSig h ω) (frField d ℓ β ν R (frPsi h ω)))) : ℝ) : ℂ) +
        srcPair g (sheetCfg h hh (frSig h ω) (frField d ℓ β ν R (frPsi h ω)))) := by
    unfold frA
    rw [← hW, Complex.ofReal_prod, ← hBw, Complex.exp_add, Complex.exp_add, Complex.exp_add,
      Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  rw [hL]
  have hR : Complex.exp (∑ x : Torus d ℓ, ∑ i : Fin N, g x i * (h i : ℂ)) *
      (W * Bw * Complex.exp (∑ x, frSiteExp h hh β ν R g x ω) *
      Complex.exp (∑ x, ∑ μ, ((frBondExp h β ν R x μ ω : ℝ) : ℂ))) =
      W * Bw * Complex.exp (∑ x : Torus d ℓ, ∑ i : Fin N, g x i * (h i : ℂ) +
        ∑ x, frSiteExp h hh β ν R g x ω + ∑ x, ∑ μ, ((frBondExp h β ν R x μ ω : ℝ) : ℂ)) := by
    rw [Complex.exp_add, Complex.exp_add]
    ring
  rw [hR]
  congr 2
  have ha : (((-(1 / 2) * ∑ x, ∑ y, frQ d ℓ ν R x y *
        inner ℝ (frPsi h ω x : E) (frPsi h ω y : E)) : ℝ) : ℂ) =
      ∑ x : Torus d ℓ, ((-(1 / 2) * ∑ y, frQ d ℓ ν R x y *
        inner ℝ (frPsi h ω x : E) (frPsi h ω y : E) : ℝ) : ℂ) := by
    rw [Finset.mul_sum, Complex.ofReal_sum]
  have hb : (((-(β * frV h ν (frSig h ω) (frField d ℓ β ν R (frPsi h ω)))) : ℝ) : ℂ) =
      ∑ x : Torus d ℓ, ((-(β * ν / 2) * (sgn (frSig h ω x) *
          tN h (frField d ℓ β ν R (frPsi h ω) x) - 1) ^ 2 : ℝ) : ℂ) +
        ∑ x, ∑ μ, ((frBondExp h β ν R x μ ω : ℝ) : ℂ) := by
    rw [neg_mul_frV, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_sum, add_comm]
    unfold frBondExp
    simp only [Complex.ofReal_sum]
  have hc : ∑ x, frSiteExp h hh β ν R g x ω =
      ∑ x : Torus d ℓ, ((-(β * ν / 2) * (sgn (frSig h ω x) *
          tN h (frField d ℓ β ν R (frPsi h ω) x) - 1) ^ 2 : ℝ) : ℂ) +
        ∑ x : Torus d ℓ, ∑ i : Fin N, g x i *
          ((((sheetPt h hh (frSig h ω x) (frField d ℓ β ν R (frPsi h ω) x) : Sph) : E) - h) i : ℂ) +
        ∑ x : Torus d ℓ, ((-(1 / 2) * ∑ y, frQ d ℓ ν R x y *
          inner ℝ (frPsi h ω x : E) (frPsi h ω y : E) : ℝ) : ℂ) := by
    unfold frSiteExp
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hsrc : srcPair g (sheetCfg h hh (frSig h ω) (frField d ℓ β ν R (frPsi h ω))) =
      ∑ x : Torus d ℓ, ∑ i : Fin N, g x i * (h i : ℂ) + ∑ x : Torus d ℓ, ∑ i : Fin N, g x i *
        ((((sheetPt h hh (frSig h ω x) (frField d ℓ β ν R (frPsi h ω) x) : Sph) : E) - h) i : ℂ) := by
    unfold srcPair sheetCfg
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PiLp.sub_apply, Complex.ofReal_sub]
    ring
  rw [ha, hb, hc, hsrc]
  ring

end

end Balaban.LargeField.KF0FR
