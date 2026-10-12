/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormPinJet
public import Balaban.SmallField.RenormTermwise
public import Balaban.SmallField.RenormTermwiseSum

/-!
# PIN-I6: the summation over polymers (3.3)

For a term family with the landed isotropic premises `PremisesTerm` (at some radius `ρ'`, used
only for the summability and cancellation identities, not for the termwise estimate), the four
renormalization conditions `SumConds`, and the reference-jet certificate `PinJet` at the data:

* `pin_renormalization`: `𝓔(y;ψ,b) - A_y(ψ) = Σ_X I(y,X)`, the series `Σ_X ‖I(y,X)‖` is
  summable with sum at most `C K₀ E₀ σ^{3-α₁} (ε/r)²`, and `Σ_y A_y = 0` on every torus;
* `pin_renormalization_scaled`: the form `C_I K₀ E₀ s^{d+α₃}`.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

theorem exp_le_wt_geom {T : TermFamily d N} {i₀ i₁ : Fin N} {E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (hP : PremisesGeom T i₀ i₁ E₀ κ A K₀ Dom)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    Real.exp (-(κ - 1) * T.dist X) ≤ wt κ X (T.dist X) := by
  unfold wt
  have hd0 := hP.dist_nonneg X hX
  have hc : (1 : ℝ) ≤ X.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, hP.zero_mem X hX⟩
  have h1 : (1 : ℝ) ≤ (X.card : ℝ) ^ 2 := one_le_pow₀ hc
  have h2 : (1 : ℝ) ≤ (1 + T.dist X) ^ 6 := one_le_pow₀ (by linarith)
  have h3 : (1 : ℝ) ≤ (X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6 := one_le_mul_of_one_le_of_one_le h1 h2
  have h4 := Real.exp_pos (-(κ - 1) * T.dist X)
  nlinarith

/-- A termwise bound by `B e^{-(κ-1) d_j(X)}` sums to at most `B K₀`. -/
theorem tsum_norm_le_of_termwise_geom {T : TermFamily d N} {i₀ i₁ : Fin N} {E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (hP : PremisesGeom T i₀ i₁ E₀ κ A K₀ Dom)
    {f : T.polys → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ X : T.polys, ‖f X‖ ≤ B * Real.exp (-(κ - 1) * T.dist X.1)) :
    Summable (fun X : T.polys => ‖f X‖) ∧ ∑' X : T.polys, ‖f X‖ ≤ B * K₀ := by
  have hle : ∀ X : T.polys, ‖f X‖ ≤ B * wt κ X.1 (T.dist X.1) := fun X =>
    (h X).trans (mul_le_mul_of_nonneg_left (exp_le_wt_geom hP X.2) hB)
  have hs : Summable (fun X : T.polys => B * wt κ X.1 (T.dist X.1)) :=
    hP.count_summable.mul_left B
  have hsum : Summable (fun X : T.polys => ‖f X‖) :=
    Summable.of_nonneg_of_le (fun X => norm_nonneg _) hle hs
  refine ⟨hsum, ?_⟩
  calc ∑' X : T.polys, ‖f X‖ ≤ ∑' X : T.polys, B * wt κ X.1 (T.dist X.1) :=
        hsum.tsum_le_tsum hle hs
    _ = B * ∑' X : T.polys, wt κ X.1 (T.dist X.1) := tsum_mul_left
    _ ≤ B * K₀ := mul_le_mul_of_nonneg_left hP.count_le hB

/-- **The corrected renormalization theorem on the pinned domain** (PIN-I6 (3.3)). -/
theorem pin_renormalization (d N : ℕ) (A Λ Ksig α₁ : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ)
    (hKsig : 0 ≤ Ksig) (hα0 : 0 < α₁) (hα1 : α₁ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν r ρ E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (_ : SumConds T i₀ i₁ ν) (_ : 0 < ρ)
      (ψ : Site d → Spin N) (b : Spin N)
      (σ ε K₂ : ℝ) (_ : DataHypAniso Dom ν σ ε K₂ ψ b),
      0 < r → r ≤ 1 → 0 < ε → ε ≤ Λ * r → 0 < σ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ ν →
      ν ≤ σ ^ 2 → 0 ≤ E₀ → K₂ ≤ Ksig * σ ^ (2 - α₁) * ε →
      (∃ (u : ℂ) (R : Matrix (Fin N) (Fin N) ℂ), Frame i₀ σ ε ψ u R ∧
        PinJet T i₀ i₁ ν r E₀ κ A Λ ψ b σ ε R) →
      energy T ψ b - Aterm T i₀ ν ψ = ∑' X : T.polys, Itw T i₀ i₁ ν X.1 ψ b ∧
      Summable (fun X : T.polys => ‖Itw T i₀ i₁ ν X.1 ψ b‖) ∧
      ∑' X : T.polys, ‖Itw T i₀ i₁ ν X.1 ψ b‖ ≤ C * K₀ * E₀ * (σ ^ (3 - α₁) * (ε / r) ^ 2) ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (ψT : Torus d ℓ → Spin N),
        ∑ y : Torus d ℓ, (1 / 2 : ℂ) * ∑' z : Site d, aCoef T i₀ ν z *
          (dot (ψT (y + liftSite ℓ z)) (ψT (y + liftSite ℓ z)) - dot (ψT y) (ψT y)) = 0 := by
  obtain ⟨C, hC0, hC⟩ := termwise_irrelevant_pin d N A Λ Ksig α₁ hA hΛ hKsig hα0 hα1
  refine ⟨C, hC0, ?_⟩
  intro T i₀ i₁ ν r ρ E₀ κ K₀ Dom hP hS hρ ψ b σ ε K₂ dat hr hr1 hε hεΛ hσ hσ1 hτ hν hνσ hE0 hK
    ⟨u, R, hF, jet⟩
  have hB0 : 0 ≤ C * E₀ * (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
    have : 0 ≤ σ ^ (3 - α₁) := (Real.rpow_pos_of_pos hσ _).le
    positivity
  have hsum := tsum_norm_le_of_termwise_geom hP.toGeom
    (f := fun X : T.polys => Itw T i₀ i₁ ν X.1 ψ b) hB0 (fun X => by
      have h := hC T i₀ i₁ ν r E₀ κ K₀ Dom hP.toGeom ψ b σ ε K₂ dat X.1 X.2 hr hr1 hε hεΛ hσ hσ1
        hτ hν hνσ hE0 hK ⟨u, R, hF, jet.term X.1 X.2⟩
      refine h.trans (le_of_eq ?_)
      ring)
  have hA' : 0 ≤ A := hA
  refine ⟨energy_sub_Aterm_eq_tsum_Itw hP hS hρ hE0 hA' dat.toDataHyp, hsum.1, ?_,
    fun ℓ _ ψT => Aterm_torus_sum_tw hP hS hρ hE0 ℓ ψT⟩
  refine hsum.2.trans (le_of_eq ?_)
  ring

/-- **The scaled form** of `pin_renormalization`: with `σ = C₀ s`, `ε/r ≤ K_R s^{(d-2)/2-γ}`,
`Σ_X ‖I(y,X)‖ ≤ C_I K₀ E₀ s^{d+α₃}`, `α₃ = 1 - 2γ - α₁`. -/
theorem pin_renormalization_scaled (d N : ℕ) (A Λ Ksig α₁ γ C₀ KR : ℝ) (hA : 0 ≤ A)
    (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hα0 : 0 < α₁) (hα1 : α₁ < 1) (hC₀ : 0 < C₀) :
    ∃ CI : ℝ, 0 ≤ CI ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν r ρ E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (_ : SumConds T i₀ i₁ ν) (_ : 0 < ρ)
      (ψ : Site d → Spin N) (b : Spin N)
      (s σ ε K₂ : ℝ) (_ : DataHypAniso Dom ν σ ε K₂ ψ b),
      0 < s → σ = C₀ * s → ε / r ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ) →
      0 < r → r ≤ 1 → 0 < ε → ε ≤ Λ * r → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ ν → ν ≤ σ ^ 2 →
      0 ≤ E₀ → K₂ ≤ Ksig * σ ^ (2 - α₁) * ε →
      (∃ (u : ℂ) (R : Matrix (Fin N) (Fin N) ℂ), Frame i₀ σ ε ψ u R ∧
        PinJet T i₀ i₁ ν r E₀ κ A Λ ψ b σ ε R) →
      energy T ψ b - Aterm T i₀ ν ψ = ∑' X : T.polys, Itw T i₀ i₁ ν X.1 ψ b ∧
      Summable (fun X : T.polys => ‖Itw T i₀ i₁ ν X.1 ψ b‖) ∧
      ∑' X : T.polys, ‖Itw T i₀ i₁ ν X.1 ψ b‖ ≤
        CI * K₀ * E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - α₁)) ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (ψT : Torus d ℓ → Spin N),
        ∑ y : Torus d ℓ, (1 / 2 : ℂ) * ∑' z : Site d, aCoef T i₀ ν z *
          (dot (ψT (y + liftSite ℓ z)) (ψT (y + liftSite ℓ z)) - dot (ψT y) (ψT y)) = 0 := by
  obtain ⟨CI, hCI0, hCI⟩ := termwise_irrelevant_pin_scaled d N A Λ Ksig α₁ γ C₀ KR hA hΛ hKsig
    hα0 hα1 hC₀
  refine ⟨CI, hCI0, ?_⟩
  intro T i₀ i₁ ν r ρ E₀ κ K₀ Dom hP hS hρ ψ b s σ ε K₂ dat hs hσs hR hr hr1 hε hεΛ hσ1 hτ hν hνσ
    hE0 hK ⟨u, R, hF, jet⟩
  have hB0 : 0 ≤ CI * E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - α₁)) := by
    have : 0 ≤ s ^ ((d : ℝ) + (1 - 2 * γ - α₁)) := (Real.rpow_pos_of_pos hs _).le
    positivity
  have hsum := tsum_norm_le_of_termwise_geom hP.toGeom
    (f := fun X : T.polys => Itw T i₀ i₁ ν X.1 ψ b) hB0 (fun X =>
      hCI T i₀ i₁ ν r E₀ κ K₀ Dom hP.toGeom ψ b s σ ε K₂ dat X.1 X.2 hs hσs hR hr hr1 hε hεΛ hσ1
        hτ hν hνσ hE0 hK ⟨u, R, hF, jet.term X.1 X.2⟩)
  refine ⟨energy_sub_Aterm_eq_tsum_Itw hP hS hρ hE0 hA dat.toDataHyp, hsum.1, ?_,
    fun ℓ _ ψT => Aterm_torus_sum_tw hP hS hρ hE0 ℓ ψT⟩
  refine hsum.2.trans (le_of_eq ?_)
  ring

end Balaban.SmallField
