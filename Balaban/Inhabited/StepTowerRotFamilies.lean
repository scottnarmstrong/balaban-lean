/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRotOld
public import Balaban.Inhabited.E0CoeffFamilyRotBlock
public import Balaban.Inhabited.E0CoeffFamilyRotMarkG

/-!
# Spin covariance of the activities and marks built from the localized old terms

`rotFam_of_term`: a function of the parameter and of the block variables of the form
`θ, Φ ↦ [θ ∈ chart ∧ ‖u‖ < corrU] · g u (θ.raw, ψ̂(Φ))` is covariant under the real orthogonal
rotation of the parameter and of the block variables when `g` is invariant under the simultaneous
rotation of the raw datum and of the hat variable.  `rotG1_of_ev` is the case of the marks
`G₁ = β ∂_t |_{t=0} ev (u, t) (θ.raw, ψ̂)`: the invariance of `ev` for `‖t‖ < bb` gives that of the
derivative.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Polymer Balaban.Inhabited.MarkBudgetAudit Matrix

section Fam

variable {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **Covariance of a family of the form `[θ ∈ chart ∧ ‖u‖ < corrU] g u (θ.raw, ψ̂(Φ))`.** -/
theorem rotFam_of_term (S : StepSetting 3 3 N₁ m₁ k 2 ϱ) {hp : 0 < S.p₁} {ρ eps : ℝ}
    (hρ : 0 < ρ) (hρp : S.p₁ ≤ ρ) {ι' : Type*}
    (Gf : physParam 2 S → ι' → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (g : ι' → ℂ → RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (S.U × Fin 2 → ℂ) → ℂ)
    (hG : ∀ θ i u Φ, Gf θ i u Φ =
      if (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) ∈
          XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < corrU then
        g i u ((θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ)
      else 0)
    (hg : ∀ i u, ‖u‖ < corrU → ∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
      ∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 eps D →
      ∀ ψh : S.U × Fin 2 → ℂ, (∀ q, ‖ψh q‖ ≤ ρ) →
      g i u (rotRaw (cmat Q) (rawOf D), rotFld (cmat Q) ψh) = g i u (rawOf D, ψh)) :
    ∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
      ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ θ' ∈ physV S S.a₁ S.ν eps,
      (θ'.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) =
        rotRaw (cmat Q) (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i, ∀ Φ ∈ physCarrier S 1 hp,
        Gf θ' i (s : ℂ) (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = Gf θ i (s : ℂ) Φ := by
  intro Q hQ θ hθ θ' hθ' hrot s hs i Φ hΦ
  obtain ⟨e', he'⟩ := exists_linearIsometryEquiv_of_orth 2 hQ
  have hfun : (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = fun b u => e' (Φ b u) :=
    funext fun b => funext fun u => (he' _).symm
  rw [hfun]
  have hs1 : ‖(s : ℂ)‖ < corrU := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    unfold corrU
    linarith [hs.2]
  obtain ⟨D₀, hD₀, hD₀θ''⟩ := hθ.1
  have hD₀θ : (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) = rawOf D₀ := hD₀θ''
  have hθ'mem : (θ'.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) ∈
      XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 eps := by
    rw [hrot]; exact rotRaw_mem hQ hθ.1
  rw [hG θ' i (s : ℂ) (fun b u => e' (Φ b u)), hG θ i (s : ℂ) Φ, ite_eq_left ⟨hθ'mem, hs1⟩,
    ite_eq_left ⟨hθ.1, hs1⟩, hrot, hD₀θ, hatOf_rot S 1 hp e' he' hρp hΦ]
  exact hg i (s : ℂ) hs1 Q hQ D₀ hD₀ _ (fun q => S.hatOf_mem 1 hρ hp Φ q)

open Classical in
/-- **Covariance of the marks `G₁ = β ∂_t|₀ ev`.** -/
theorem rotG1_of_ev (S : StepSetting 3 3 N₁ m₁ k 2 ϱ) {hp : 0 < S.p₁} {ρ eps bb : ℝ}
    (hρ : 0 < ρ) (hρp : S.p₁ ≤ ρ) (hbb : 0 < bb) {ι' : Type*}
    (G : physParam 2 S → ι' → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (ev : ι' → ℂ → ℂ → RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (S.U × Fin 2 → ℂ) → ℂ)
    (hG : ∀ θ i u Φ, G θ i u Φ =
      if (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) ∈
          XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < corrU then
        (S.β : ℂ) * deriv (fun t : ℂ => ev i u t
          ((θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ)) 0
      else 0)
    (hev : ∀ i u t, ‖u‖ < corrU → ‖t‖ < bb → ∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
      ∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 eps D →
      ∀ ψh : S.U × Fin 2 → ℂ, (∀ q, ‖ψh q‖ ≤ ρ) →
      ev i u t (rotRaw (cmat Q) (rawOf D), rotFld (cmat Q) ψh) = ev i u t (rawOf D, ψh)) :
    ∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
      ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ θ' ∈ physV S S.a₁ S.ν eps,
      (θ'.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) =
        rotRaw (cmat Q) (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i, ∀ Φ ∈ physCarrier S 1 hp,
        G θ' i (s : ℂ) (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = G θ i (s : ℂ) Φ := by
  refine rotFam_of_term S hρ hρp G (fun i u x => (S.β : ℂ) * deriv (fun t : ℂ => ev i u t x) 0)
    hG ?_
  intro i u hu Q hQ D hD ψh hψh
  refine congrArg (fun w => (S.β : ℂ) * w) (Filter.EventuallyEq.deriv_eq ?_)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hbb] with t ht
  exact hev i u t hu (mem_ball_zero_iff.1 ht) Q hQ D hD ψh hψh

end Fam

end Balaban.Inhabited
