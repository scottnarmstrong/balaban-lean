/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfAssemble
public import Balaban.Spine.FinalSfConstTerm

/-!
# `FinalSmallFieldInput` from the Gaussian average of the fluctuation integrand

A6-3, assembly (item 2). At the constant configuration `ψ_k ≡ h` the exponent `𝒜_k + ℱ_k` of the
small-field factor of the whole torus is the vacuum term, the source term `⟨g, h⟩` and the inherited
observable activities (`const_exponent`). Dividing the Gaussian integrand `sfGaussIntegrand` (centre
`ψ₀ ≡ h`) by `exp` of this exponent leaves the *fluctuation integrand*, and `FinalSmallFieldInput`
reduces to the statement `FinalSfFluctInput` that the Gaussian average of the fluctuation integrand
is the exponential of a vacuum term and of the sum of scale-`(k+1)` activities
(`finalSmallFieldInput_of_fluctForm`).

`FinalSfFluctInput` is the content of the three open items of A6-3 (a) and (d): the integrand is
`χ_k exp(-β_k V³ + [ℰ_k - ℰ_k(h)] + [ℱ_k - ℱ_k(h)] + ℛ^{(k)} - …)` with the cubic remainder
`V³ = A*_k - ½⟨v, H v⟩` (`sfGaussIntegrand_cubic`), which has to be shown volume uniform and localized
(PHYS-CUBIC); the Gaussian average of its exponential is a polymer exponential by the polymer
expansion with the cut `χ_k` (`cutoffInteraction_final_*`, `abstract_expansion_taggedCfin_final`),
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
noncomputable def vacConst (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) : ℂ :=
  EresK2 C vc Set.univ (fun _ => hv) hv -
    ((C.sf.E C.N₁ * volK M (Set.univ : Set (Torus S.d (n k))) : ℝ) : ℂ)

end Vac

section Inputs

variable (d N : ℕ) (δ : ℝ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **The Gaussian average of the fluctuation integrand** (A6-3 (a) and (d), the statement left
open): for a member of `ℛ♭_k` at the stopping scale there are activities `a` of the scale `k + 1`
(with the exact two-torus agreement) and a vacuum term such that, on every torus and for every source
of the unit `ℓ¹` ball, the Gaussian average, at a positive definite form `K`, of the integrand
`sfGaussIntegrand` (centre `ψ₀ ≡ h`) divided by `exp(𝒜_k + ℱ_k)` at the constant configuration is the
exponential of the vacuum term and the sum of the activities `a`. -/
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
        ∃ (Kq : Matrix (BlockAt 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK)
              (T κ c₉).M (kf + 1) k × Fin N)
            (BlockAt 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK)
              (T κ c₉).M (kf + 1) k × Fin N) ℝ),
          Kq.PosDef ∧
          (pdGaussNorm (BlockAt 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK)
              (T κ c₉).M (kf + 1) k × Fin N) ℝ Kq : ℂ) *
            ∫ w, sfGaussIntegrand (F.ctx hM6 hkK nK) vc Set.univ h g Kq (fun _ => h) w *
                Complex.exp (-(Ares2 (F.ctx hM6 hkK nK) vc Set.univ (fun _ => h) h +
                  (F.ctx hM6 hkK nK).Fres Set.univ (fun _ => h) h g))
              ∂(pdGaussian (BlockAt 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
                (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M (kf + 1) k × Fin N) ℝ) =
            Complex.exp (E nK + ∑ X, a ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) *
                  (T κ c₉).L ^ (kf + 1)) (k + 1) X (fun x i => g (x, i)))

/-- **`FinalSmallFieldInput` from the Gaussian average of the fluctuation integrand**
(A6-3, assembly). -/
theorem finalSmallFieldInput_of_fluctForm (hPre : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (hsep : ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
      bgR0 d (T κ c₉).L ≤ minSep (T κ c₉).L (M1 κ c₉))
    (hG : FinalSfFluctInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ) :
    FinalSmallFieldInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ hκ c₉ hc₉
  obtain ⟨β₁, h₁⟩ := hG κ hκ c₉ hc₉
  obtain ⟨β₂, h₂⟩ := measInt_sfFactor2_of_flatRep d N δ T P6 C7 PB cs₀ M1 c rH ϱ hPre hsep κ hκ c₉ hc₉
  refine ⟨max β₁ β₂, fun β hβ ν hν hνL h hh kf hkf _ _ k hk1 hkkf ρ νk hM6 hkK R geo cs P F St vc
    hF hstop => ?_⟩
  obtain ⟨a, E, hA, hid⟩ := h₁ β ((le_max_left _ _).trans hβ) ν hν hνL h hh kf hkf k hk1 hkkf ρ νk
    hM6 hkK R geo cs P F St vc hF hstop
  refine ⟨a, fun nK => if hnK : nK ≠ 0 then
    (haveI : NeZero nK := ⟨hnK⟩; E nK + vacConst (F.ctx hM6 hkK nK) vc h) else 0, hA,
    fun nK _ g hg => ?_⟩
  have hnK : nK ≠ 0 := NeZero.ne nK
  obtain ⟨Kq, hK, heq⟩ := hid nK g hg
  obtain ⟨HB, hm, -⟩ := h₂ β ((le_max_right _ _).trans hβ) ν hν hνL h hh kf hkf k hk1 hkkf ρ νk hM6
    hkK R geo cs P F St vc hF hstop nK g hg
  rw [sfIntegral_eq_gauss F hM6 hkK vc h nK g hK (fun _ => h) hm]
  beta_reduce
  simp only [ne_eq, hnK, not_false_eq_true, ↓reduceDIte]
  have he : ∑ i, h i ^ 2 = 1 := sum_sq_eq_one_of_norm_eq_one h hh
  have hX := const_exponent (F.ctx hM6 hkK nK) h vc HB he hk1 g
  set X₀ := Ares2 (F.ctx hM6 hkK nK) vc Set.univ (fun _ => h) h +
    (F.ctx hM6 hkK nK).Fres Set.univ (fun _ => h) h g with hX₀
  have hint : ∫ w, sfGaussIntegrand (F.ctx hM6 hkK nK) vc Set.univ h g Kq (fun _ => h) w
        ∂(pdGaussian _ ℝ) =
      Complex.exp X₀ * ∫ w, sfGaussIntegrand (F.ctx hM6 hkK nK) vc Set.univ h g Kq (fun _ => h) w *
        Complex.exp (-X₀) ∂(pdGaussian _ ℝ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    beta_reduce
    rw [mul_left_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  rw [hint]
  calc (pdGaussNorm _ ℝ Kq : ℂ) * (Complex.exp X₀ * ∫ w, sfGaussIntegrand (F.ctx hM6 hkK nK) vc
        Set.univ h g Kq (fun _ => h) w * Complex.exp (-X₀) ∂(pdGaussian _ ℝ))
      = Complex.exp X₀ * ((pdGaussNorm _ ℝ Kq : ℂ) * ∫ w, sfGaussIntegrand (F.ctx hM6 hkK nK) vc
        Set.univ h g Kq (fun _ => h) w * Complex.exp (-X₀) ∂(pdGaussian _ ℝ)) := by ring
    _ = _ := by
        rw [heq, ← Complex.exp_add]
        congr 1
        have hX' : X₀ = vacConst (F.ctx hM6 hkK nK) vc h +
            (∑ y : Torus d ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) *
                (T κ c₉).L ^ (kf + 1)), ∑ i : Fin N, g (y, i) * (h i : ℂ)) +
            ∑ j ∈ Finset.Icc 1 k, ∑ X : Finset (Torus d ((T κ c₉).M *
                sides (T κ c₉).L (kf + 1) nK (kf + 1) * (T κ c₉).L ^ (kf + 1))),
              inhObs F.sf (P6 κ c₉).m₀ h ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) *
                (T κ c₉).L ^ (kf + 1)) j X (fun x i => g (x, i)) := hX
        rw [hX']
        ring

end Inputs

end Balaban.RootFSpine
