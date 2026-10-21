/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfIntegrable
public import Balaban.Spine.FinalSfGauss

/-!
# `FinalSmallFieldInput` from its Gaussian form

A6-3, assembly (item 2). The small-field integral `Ξ^sf = ∫ sfFactor2 dψ_k` of a member of `ℛ♭_k` at
the stopping scale is a Gaussian average: for every positive definite form `K` and centre `ψ₀`,
`Ξ^sf = Z_K ∫ sfGaussIntegrand dγ` (`integral_sfFactor2_gauss`; the measurability of `sfFactor2` is
`measInt_sfFactor2_of_flatRep`, for `β` large). `finalSmallFieldInput_of_gaussForm` reduces
`FinalSmallFieldInput` to the statement `FinalSfGaussInput` that the Gaussian average of the
integrand `sfGaussIntegrand` (at a form `K = β_k H`, `H` the final Hessian, and the centre `ψ₀ = h`) is
the exponential of the vacuum term, the constant source term `⟨g, h⟩`, the inherited observable
activities `q_j` (the values of `ℱ_k` and `ℰ_k` at the constant configuration, `Fres_const_univ`,
`EresK2_const_univ`) and the scale-`(k+1)` activities `a`. The content of `FinalSfGaussInput` is
exactly the three open items of A6-3 (a) and (d): the volume-uniform cubic remainder `V³ = A*_k -
½⟨v, H v⟩` (PHYS-CUBIC; `sfGaussIntegrand_cubic` isolates it), the polymer expansion of the
resulting integrand with the cut `χ_k` (`cutoffInteraction_final_*`, `abstract_expansion_taggedCfin_final`),
and the exact two-torus agreement of `a` (the clause `ActAgree` of `ObservableActivitiesAt`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField
  Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Localization Balaban.Green

namespace Balaban.RootFSpine

section Inputs

variable (d N : ℕ) (δ : ℝ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **`FinalSmallFieldInput` in Gaussian form**: as `FinalSmallFieldInput`, with the integral
`Ξ^sf = sfIntegral` replaced by the Gaussian average `Z_K ∫ sfGaussIntegrand dγ` at some positive
definite form `K` and some centre `ψ₀` (the value does not depend on them,
`integral_sfFactor2_gauss`). This is the statement left open by the analysis of A6-3 (a): the
cubic remainder, the polymer expansion with the cut, and the two-torus agreement of the activities. -/
def FinalSfGaussInput : Prop :=
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
              (T κ c₉).M (kf + 1) k × Fin N) ℝ)
          (ψ0 : BlockAt 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK)
              (T κ c₉).M (kf + 1) k → EuclideanSpace ℝ (Fin N)),
          Kq.PosDef ∧
          (pdGaussNorm (BlockAt 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK)
              (T κ c₉).M (kf + 1) k × Fin N) ℝ Kq : ℂ) *
            ∫ w, sfGaussIntegrand (F.ctx hM6 hkK nK) vc Set.univ h g Kq ψ0 w
              ∂(pdGaussian (BlockAt 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
                (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M (kf + 1) k × Fin N) ℝ) =
            Complex.exp (E nK + ∑ x, ∑ i, g (x, i) * (h i : ℂ)
              + ∑ j ∈ Finset.Icc 1 k, ∑ X,
                inhObs F.sf (P6 κ c₉).m₀ h
                  ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) * (T κ c₉).L ^ (kf + 1)) j X
                  (fun x i => g (x, i))
              + ∑ X, a ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) *
                  (T κ c₉).L ^ (kf + 1)) (k + 1) X (fun x i => g (x, i)))

/-- **`FinalSmallFieldInput` from its Gaussian form** (A6-3, assembly): `Ξ^sf` is the Gaussian
average (`sfIntegral_eq_gauss`, the measurability of `sfFactor2` from
`measInt_sfFactor2_of_flatRep`). The premises beyond `FinalSfGaussInput` are the prefix (`hPre`) and
the typing premise that the cube generating sets are separated by at least `R₀(d, L)`: `hsep`,
`bgR0 d L ≤ 5 L M₁`. -/
theorem finalSmallFieldInput_of_gaussForm (hPre : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (hsep : ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
      bgR0 d (T κ c₉).L ≤ minSep (T κ c₉).L (M1 κ c₉))
    (hG : FinalSfGaussInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ) :
    FinalSmallFieldInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ hκ c₉ hc₉
  obtain ⟨β₁, h₁⟩ := hG κ hκ c₉ hc₉
  obtain ⟨β₂, h₂⟩ := measInt_sfFactor2_of_flatRep d N δ T P6 C7 PB cs₀ M1 c rH ϱ hPre hsep κ hκ c₉ hc₉
  refine ⟨max β₁ β₂, fun β hβ ν hν hνL h hh kf hkf _ _ k hk1 hkkf ρ νk hM6 hkK R geo cs P F St vc
    hF hstop => ?_⟩
  obtain ⟨a, E, hA, hid⟩ := h₁ β ((le_max_left _ _).trans hβ) ν hν hνL h hh kf hkf k hk1 hkkf ρ νk
    hM6 hkK R geo cs P F St vc hF hstop
  refine ⟨a, E, hA, fun nK _ g hg => ?_⟩
  obtain ⟨Kq, ψ0, hK, heq⟩ := hid nK g hg
  have hm := (h₂ β ((le_max_right _ _).trans hβ) ν hν hνL h hh kf hkf k hk1 hkkf ρ νk hM6 hkK R geo
    cs P F St vc hF hstop nK g hg).1
  rw [sfIntegral_eq_gauss F hM6 hkK vc h nK g hK ψ0 hm]
  exact heq

end Inputs

end Balaban.RootFSpine
