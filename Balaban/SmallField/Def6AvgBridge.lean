/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgMoment
public import Balaban.SmallField.RenormTermwiseCrude
public import Balaban.SmallField.RenormTermwise

/-!
# Reynolds averaging: the bridge from the class to the termwise I-6

CLASS-RULINGS Q-A, "Proof and repair of the centred I-6 symmetry".  For a member of the class
(`IsSFFamily`) with the numerical conditions `MomNum`:

* `IsSFFamily.sumCondsAvg`: the averaged family satisfies the renormalization conditions
  (H.5)(1)-(4) of I-6 (`SumConds`);
* `IsSFFamily.bridgeAvg`: it therefore satisfies the full I-6 premises `Premises` (the termwise
  premises `premisesTermAvg`, including the point-group invariance, together with `SumConds`);
* `IsSFFamily.energy_sub_Aterm_avg`, `IsSFFamily.termwise_irrelevant_avg`: the landed termwise
  decomposition `energy_sub_Aterm_eq_tsum_Itw` and the termwise irrelevance bound
  `termwise_irrelevant_all_scales` apply to the averaged family of a class member (with the isotropic
  radius `liftRadius`; the anisotropic radius of CLASS-RULINGS Q-D is a separate package).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

/-- **`SumConds` for the Reynolds-averaged family** (CLASS-RULINGS Q-A, Q-B, Q-C): the first three
conditions from the infinite-volume conditions `val`, `dh`, `dpsi` of `RenormCond` through the
translation invariance of the density at constant data, the second moment from the thermodynamic
condition `moment` at every centre of the box of paving offsets. -/
theorem IsSFFamily.sumCondsAvg (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    SumConds (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)) i₀ i₁
      (nuIdeal L k (ν k) j) :=
  ⟨avgFamily_ren_val hF hn hne, avgFamily_ren_b hF hn hne, avgFamily_ren_psi hF hn hne,
    avgFamily_moment hF hn hne⟩

/-- **The bridge from the class to the I-6 premises** (CLASS-RULINGS Q-A): a member of the class
supplies the full premises `Premises` of I-6 for the Reynolds average over paving offsets and the
point group of the terms of `T∞`, with the weighted polymer-count constant multiplied by the number
`(L^{m₀+m₁})^d` of paving offsets. -/
theorem IsSFFamily.bridgeAvg (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    Premises (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)) i₀ i₁
      (nuIdeal L k (ν k) j) (liftRadius d L N P j) P.E₀ P.κ (diamA d L P.m₀ m₁)
      (((L : ℝ) ^ (P.m₀ + m₁)) ^ d * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
        (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)))
      (avgDom P β ν a Tm j i₀ (nuIdeal L k (ν k) j)) :=
  (hF.premisesTermAvg hn hne).toPremises (hF.sumCondsAvg hn hne)

/-- **The termwise decomposition for a class member** (Lemma 3.2): on data in the data domain of the
averaged family, `𝓔(y;ψ,b) - A_y(ψ) = Σ_X I(y,X;ψ,b)`. -/
theorem IsSFFamily.energy_sub_Aterm_avg (hF : IsSFFamily P β ν a Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {ψ : Site d → Spin N} {b : Spin N} {σ ε K₂ : ℝ}
    (dat : DataHyp (avgDom P β ν a Tm j i₀ (nuIdeal L k (ν k) j)) (nuIdeal L k (ν k) j) σ ε K₂ ψ b) :
    energy (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)) ψ b -
        Aterm (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)) i₀
          (nuIdeal L k (ν k) j) ψ =
      ∑' X : (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys,
        Itw (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)) i₀ i₁
          (nuIdeal L k (ν k) j) X.1 ψ b :=
  energy_sub_Aterm_eq_tsum_Itw (hF.premisesTermAvg hn hne) (hF.sumCondsAvg hn hne)
    (liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀)
    hF.admissible.E₀_nonneg (diamA_nonneg d L P.m₀ m₁) dat

/-- **Termwise irrelevance for a class member** (Lemma 3.2 (iii), all scales): the landed bound
`termwise_irrelevant_all_scales` applies to the averaged family of a member of the class, with the
isotropic radius `liftRadius`. -/
theorem IsSFFamily.termwise_irrelevant_avg (hF : IsSFFamily P β ν a Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    (Λ Ksig α₁ γ C₀ KR : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hα0 : 0 < α₁) (hα1 : α₁ < 1)
    (hC₀ : 0 < C₀) (hα₃ : 0 ≤ (d : ℝ) + (1 - 2 * γ - α₁)) :
    ∃ CI : ℝ, 0 ≤ CI ∧ ∀ (ψ : Site d → Spin N) (b : Spin N) (s σ ε K₂ : ℝ)
      (_ : DataHyp (avgDom P β ν a Tm j i₀ (nuIdeal L k (ν k) j)) (nuIdeal L k (ν k) j) σ ε K₂ ψ b)
      (X : Finset (Site d))
      (_ : X ∈ (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys),
      0 < s → s ≤ 1 → σ = C₀ * s →
      ε / liftRadius d L N P j ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ) →
      liftRadius d L N P j ≤ 1 → 0 < ε → ε ≤ Λ * liftRadius d L N P j → σ ^ 2 * ε ≤ 1 / 4 →
      0 ≤ nuIdeal L k (ν k) j → nuIdeal L k (ν k) j ≤ σ ^ 2 →
      K₂ ≤ Ksig * σ ^ (2 - α₁) * ε →
      ‖Itw (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)) i₀ i₁
          (nuIdeal L k (ν k) j) X ψ b‖ ≤
        CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - α₁)) *
          Real.exp (-(P.κ - 1) * (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
            (liftRadius d L N P j)).dist X) := by
  obtain ⟨CI, hCI, h⟩ := termwise_irrelevant_all_scales d N (diamA d L P.m₀ m₁) Λ Ksig α₁ γ C₀ KR
    (diamA_nonneg d L P.m₀ m₁) hΛ hKsig hα0 hα1 hC₀ hα₃
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  refine ⟨CI, hCI, fun ψ b s σ ε K₂ dat X hX hs hs1 hσs hR hρ1 hε hεΛ hτ hν hνσ hK => ?_⟩
  exact h _ i₀ i₁ _ _ P.E₀ P.κ _ _ (hF.premisesTermAvg hn hne) ψ b s σ ε K₂ dat X hX hs hs1 hσs hR
    hρ0 hρ1 hε hεΛ hτ hν hνσ hF.admissible.E₀_nonneg hK

end Balaban.SmallField.Def6
