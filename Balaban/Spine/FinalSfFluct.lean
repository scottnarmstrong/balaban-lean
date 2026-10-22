/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfIntegrable
public import Balaban.Spine.FinalSfConstTerm

/-!
# `FinalSmallFieldInput` from the box average of the fluctuation integrand

A6-3, assembly (item 2). At the constant configuration `ψ_k ≡ h` the exponent `X₀ = 𝒜_k + ℱ_k` of
the small-field factor of the whole torus (`constExponent`) is the vacuum term, the source term
`⟨g, h⟩` and the inherited observable activities (`const_exponent`). Dividing the Gaussian integrand
`sfGaussIntegrand` (form `K = β_k D`, centre `ψ₀ ≡ h`) by `exp(X₀)` leaves the *fluctuation
integrand*; its box average is `ctxFluctBoxIntegral`, and the box integral `Ξ_box` of the torus is
`exp(X₀)` times it (`ctxBoxIntegral_eq_exp_mul`, for every complex `X₀`). Both are stated at every
whitening `A` of the Gaussian variable (`ctxFluctBoxIntegralL`, `ctxBoxIntegralL_eq_exp_mul`; P5
(2.39)), the exact whitening `K^{-1/2}` being the instance. `FinalSmallFieldInput`
reduces to the statement `FinalSfFluctInput` that the box average of the fluctuation integrand is the
exponential of a vacuum term and of the sum of scale-`(k+1)` activities
(`finalSmallFieldInput_of_fluctForm`).

`FinalSfFluctInput` is the content of the open items of A6-3 (a) and (d): on the box the
fluctuation integrand is `χ_k exp(-β_k V³ + [ℰ_k - ℰ_k(h)] + [ℱ_k - ℱ_k(h)] + ℛ^{(k)} - …)` with the
cubic remainder `V³ = A*_k - ½⟨v, H v⟩` (`sfGaussIntegrand_cubic`), which has to be localized
(PHYS-CUBIC); the box average of its exponential is a polymer exponential by the polymer expansion
over the product measure of the box (the local form of `Spine/FinalBoxLocal.lean` and the gas layer),
with the first-order response of `φ̄_k` giving the quadratic-in-`g` scale-`(k+1)` term
(`gauss_source_linear`); and the activities `a` satisfy the exact two-torus agreement (the clause
`ActAgree` of `ObservableActivitiesAt`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField
  Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Localization Balaban.Green

namespace Balaban.RootFSpine

section Vac

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- **The vacuum term of the small-field factor at the constant configuration**
(`ℰ_k(h) - E_k |T|_k`, independent of the source). -/
noncomputable def fluctVacConst (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) : ℂ :=
  EresK2 C vc Set.univ (fun _ => hv) hv -
    ((C.sf.E C.N₁ * volK M (Set.univ : Set (Torus S.d (n k))) : ℝ) : ℂ)

/-- **The exponent at the constant configuration** `X₀(g) = (𝒜_k + ℱ_k)(T; ψ_k ≡ h, h, g)` of the
small-field factor of the whole torus (without `ℛ^{(k)}`). -/
noncomputable def constExponent (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) : ℂ :=
  Ares2 C vc Set.univ (fun _ => hv) hv + C.Fres Set.univ (fun _ => hv) hv g

/-- **The box average of the fluctuation integrand of one torus at a whitening** `A`:
`|det A| (2π)^{n/2} ∫_{box(p₁)} sfGaussIntegrandL(w) mismatch(w) exp(-X₀(g)) dγ(w)`, at the form
`K = β_k D` (`sfFinalK`) and the centre `ψ₀ ≡ h`. -/
noncomputable def ctxFluctBoxIntegralL (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N))
    (A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ) (p1 : ℝ)
    (g : GIdx S n M K N → ℂ) : ℂ :=
  (whitenNorm A : ℂ) *
    ∫ w in gaussBox (BlockAt S n M K k × Fin N) p1,
      sfGaussIntegrandL C vc Set.univ hv g (sfFinalK C hv) A (fun _ => hv) w *
        (mismatchFactor (sfFinalK C hv) A w : ℂ) * Complex.exp (-constExponent C vc hv g)
      ∂(Green.pdGaussian (BlockAt S n M K k × Fin N) ℝ)

/-- **The box average of the fluctuation integrand** of one torus at the exact whitening
`K^{-1/2}`, `K = β_k D` (`sfFinalK`), centre `ψ₀ ≡ h` (`ctxFluctBoxIntegralL`). -/
noncomputable def ctxFluctBoxIntegral (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) (p1 : ℝ) (g : GIdx S n M K N → ℂ) : ℂ :=
  ctxFluctBoxIntegralL C vc hv (Green.pdSqrtInv (sfFinalK C hv)) p1 g

/-- **The box integral is `exp(X₀)` times the box average of the integrand divided by `exp(X₀)`**,
at every whitening and for every complex `X₀`. -/
theorem ctxBoxIntegralL_eq_exp_mul_of (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N))
    (A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ) (p1 : ℝ)
    (g : GIdx S n M K N → ℂ) (X₀ : ℂ) :
    ctxBoxIntegralL C vc hv A p1 g = Complex.exp X₀ *
      ((whitenNorm A : ℂ) *
        ∫ w in gaussBox (BlockAt S n M K k × Fin N) p1,
          sfGaussIntegrandL C vc Set.univ hv g (sfFinalK C hv) A (fun _ => hv) w *
            (mismatchFactor (sfFinalK C hv) A w : ℂ) * Complex.exp (-X₀)
            ∂(Green.pdGaussian (BlockAt S n M K k × Fin N) ℝ)) := by
  have e : ∫ w in gaussBox (BlockAt S n M K k × Fin N) p1,
        sfGaussIntegrandL C vc Set.univ hv g (sfFinalK C hv) A (fun _ => hv) w *
          (mismatchFactor (sfFinalK C hv) A w : ℂ)
        ∂(Green.pdGaussian (BlockAt S n M K k × Fin N) ℝ) =
      Complex.exp X₀ * ∫ w in gaussBox (BlockAt S n M K k × Fin N) p1,
        sfGaussIntegrandL C vc Set.univ hv g (sfFinalK C hv) A (fun _ => hv) w *
          (mismatchFactor (sfFinalK C hv) A w : ℂ) * Complex.exp (-X₀)
          ∂(Green.pdGaussian (BlockAt S n M K k × Fin N) ℝ) := by
    rw [← integral_const_mul]
    congr 1
    funext w
    rw [mul_left_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  unfold ctxBoxIntegralL
  rw [e]
  ring

/-- **`Ξ_box = exp(X₀) · (box average of the fluctuation integrand)`** at the constant-configuration
exponent `X₀ = constExponent`, at every whitening. -/
theorem ctxBoxIntegralL_eq_exp_mul (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N))
    (A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ) (p1 : ℝ)
    (g : GIdx S n M K N → ℂ) :
    ctxBoxIntegralL C vc hv A p1 g =
      Complex.exp (constExponent C vc hv g) * ctxFluctBoxIntegralL C vc hv A p1 g :=
  ctxBoxIntegralL_eq_exp_mul_of C vc hv A p1 g _

/-- **`Ξ_box = exp(X₀) · (box average of the fluctuation integrand)`** at the exact whitening (the
instance of `ctxBoxIntegralL_eq_exp_mul`). -/
theorem ctxBoxIntegral_eq_exp_mul (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) (p1 : ℝ) (g : GIdx S n M K N → ℂ) :
    ctxBoxIntegral C vc hv p1 g =
      Complex.exp (constExponent C vc hv g) * ctxFluctBoxIntegral C vc hv p1 g :=
  ctxBoxIntegralL_eq_exp_mul C vc hv _ p1 g

/-- **The box integral from the box average of the fluctuation integrand** on one torus, at every
whitening `A`: if `ctxFluctBoxIntegralL = exp(E' + S')`, then `Ξ_box(A)` is the exponential of
`E' +` the vacuum term `+ ⟨g, h⟩ +` the inherited activities `+ S'` (`ctxBoxIntegralL_eq_exp_mul`,
`const_exponent`). -/
theorem ctxBoxIntegralL_eq_exp_of_fluct (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N))
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.muBg k))
    (he : ∑ i, hv i ^ 2 = 1) (hk : 1 ≤ k)
    (A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ) (p1 : ℝ)
    (g : GIdx S n M K N → ℂ) {E' S' : ℂ}
    (hfl : ctxFluctBoxIntegralL C vc hv A p1 g = Complex.exp (E' + S')) :
    ctxBoxIntegralL C vc hv A p1 g = Complex.exp ((E' + fluctVacConst C vc hv) +
      (∑ y : Torus S.d (M * n K * S.L ^ K), ∑ i : Fin N, g (y, i) * (hv i : ℂ)) +
      ∑ j ∈ Finset.Icc 1 k, ∑ X : Finset (Torus S.d (M * n K * S.L ^ K)),
        inhObs C.sf C.m₀ hv (M * n K * S.L ^ K) j X (fun x i => g (x, i)) + S') := by
  rw [ctxBoxIntegralL_eq_exp_mul, hfl, ← Complex.exp_add]
  unfold constExponent
  rw [const_exponent C hv vc H he hk g]
  unfold fluctVacConst
  congr 1
  ring

end Vac

section Inputs

variable (d N : ℕ) (δ : ℝ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ) (cut : ℝ → ℝ → ℝ → ℝ)

/-- **The box average of the fluctuation integrand** (A6-3 (a) and (d), the statement left
open): for a member of `ℛ♭_k` at the stopping scale there are activities `a` of the scale `k + 1`
(with the exact two-torus agreement) and a vacuum term such that, on every torus and for every source
of the unit `ℓ¹` ball, the box average (cutoff `p₁ = cut κ c₉ β_k`) of the integrand `sfGaussIntegrand`
(form `K = β_k D`, centre `ψ₀ ≡ h`) divided by `exp(𝒜_k + ℱ_k)` at the constant configuration
(`ctxFluctBoxIntegral`) is the exponential of the vacuum term and the sum of the activities `a`. -/
def FinalSfFluctInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k ≤ kf →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ) hM6 hkK R geo cs P F St vc,
    FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk →
    7 / 8 < νk * ((T κ c₉).L : ℝ) ^ 2 →
    ∃ (a : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (E : ℕ → ℂ),
      ObservableActivitiesAt d N (T κ c₉).L (T κ c₉).M κ (c₉ / 2) δ (k + 1) kf a ∧
      ∀ (nK : ℕ) [NeZero nK]
        (g : GIdx 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) N → ℂ), g ∈ LargeField.l1Ball _ →
        ctxFluctBoxIntegral (F.ctx hM6 hkK nK) vc h (cut κ c₉ (F.sf.β k)) g =
          Complex.exp (E nK + ∑ X, a ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) *
            (T κ c₉).L ^ (kf + 1)) (k + 1) X (fun x i => g (x, i)))

/-- **`FinalSmallFieldInput` from the box average of the fluctuation integrand**
(A6-3, assembly): `Ξ_box = exp(X₀) · (box average)` (`ctxBoxIntegral_eq_exp_mul`) and `X₀` is the
vacuum term, `⟨g, h⟩` and the inherited activities (`const_exponent`, with the hypothesis `BgHyp` of
the cube from `measInt_sfFactor2_of_flatRep`). -/
theorem finalSmallFieldInput_of_fluctForm (hPre : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (hG : FinalSfFluctInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ cut) :
    FinalSmallFieldInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ cut := by
  intro κ hκ c₉ hc₉
  obtain ⟨β₁, h₁⟩ := hG κ hκ c₉ hc₉
  obtain ⟨β₂, h₂⟩ := measInt_sfFactor2_of_flatRep d N δ T P6 C7 PB cs₀ M1 c rH ϱ hPre κ hκ c₉ hc₉
  refine ⟨max β₁ β₂, fun β hβ ν hν hνL h hh kf hkf _ _ k hk1 hkkf ρ νk hM6 hkK R geo cs P F St vc
    hF hstop => ?_⟩
  obtain ⟨a, E, hA, hid⟩ := h₁ β ((le_max_left _ _).trans hβ) ν hν hνL h hh kf hkf k hk1 hkkf ρ νk
    hM6 hkK R geo cs P F St vc hF hstop
  refine ⟨a, fun nK => if hnK : nK ≠ 0 then
    (haveI : NeZero nK := ⟨hnK⟩; E nK + fluctVacConst (F.ctx hM6 hkK nK) vc h) else 0, hA,
    fun nK _ g hg => ?_⟩
  have hnK : nK ≠ 0 := NeZero.ne nK
  obtain ⟨HB, -, -⟩ := h₂ β ((le_max_right _ _).trans hβ) ν hν hνL h hh kf hkf k hk1 hkkf ρ νk hM6
    hkK R geo cs P F St vc hF hstop nK g hg
  have he : ∑ i, h i ^ 2 = 1 := sum_sq_eq_one_of_norm_eq_one h hh
  rw [sfBoxIntegral, ctxBoxIntegral, ctxBoxIntegralL_eq_exp_of_fluct (F.ctx hM6 hkK nK) vc h HB he
    hk1 _ _ g (E' := E nK) (S' := ∑ X, a ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) *
      (T κ c₉).L ^ (kf + 1)) (k + 1) X (fun x i => g (x, i))) (hid nK g hg)]
  simp only [ne_eq, hnK, not_false_eq_true, ↓reduceDIte]
  rfl

end Inputs

end Balaban.RootFSpine
