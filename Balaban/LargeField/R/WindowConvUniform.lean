/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvSource

/-!
# A uniform terminal comparison for converted window pieces

The supported local/window comparison is retained as a named hypothesis. Its uniform
form suffices for the existing finite window theorem, by choosing a zero exponential
rate in that theorem. In particular this does not assert the physical P7 (2.14) response.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.SmallField

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L]
  {U : Type*} {S : Set U} {ι : Type*} [Fintype ι]
  {sc : ι → ℕ} {k1 k : ℕ}

/-- The exact terminal coefficient carried by each piece, compared with the common
window coefficient. This specializes the chain invariant without identifying the
piece-dependent coefficient with `W.ak`. -/
theorem PieceWindowSetup.coeff_target_mismatch
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k) (i : ι) (ℓ : ℕ) :
    (W.chain i).β k * ((W.chain i).a k ℓ - W.ak ℓ) =
      (W.chain i).β (sc i + 1) * (W.chain i).a (sc i + 1) ℓ -
        (W.chain i).β k * W.ak ℓ :=
  (W.chain i).coeff_target_mismatch (by have := W.sc_lt i; omega) W.ak ℓ

/-- Four separately charged terminal comparisons give the corrected uniform
`window_decay` input. The intermediate actions can be the normalized local action,
its coefficient-adjusted action, and its mass-adjusted window action; each physical
comparison remains an explicitly named premise. -/
theorem PieceWindowSetup.window_uniform_of_parts
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)
    (P Q R : ι → U → ℂ) (Kpair Kcoef Kswitch Kread : ℝ)
    (hpair : ∀ i, ∀ u ∈ S,
      ‖(W.chain i).T u k - P i u‖ ≤ Kpair * W.mcount i)
    (hcoef : ∀ i, ∀ u ∈ S,
      ‖P i u - Q i u‖ ≤ Kcoef * W.mcount i)
    (hswitch : ∀ i, ∀ u ∈ S,
      ‖Q i u - R i u‖ ≤ Kswitch * W.mcount i)
    (hread : ∀ i, ∀ u ∈ S,
      ‖R i u - (W.βk : ℂ) *
        actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)‖ ≤
        Kread * W.mcount i) :
    ∀ i, ∀ u ∈ S,
      ‖(W.chain i).T u k - (W.βk : ℂ) *
        actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)‖ ≤
          (Kpair + Kcoef + Kswitch + Kread) * W.mcount i := by
  intro i u hu
  let T := (W.chain i).T u k
  let V := (W.βk : ℂ) * actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)
  have heq : T - V = (T - P i u) + (P i u - Q i u) +
      (Q i u - R i u) + (R i u - V) := by ring
  change ‖T - V‖ ≤ _
  rw [heq]
  calc
    ‖(T - P i u) + (P i u - Q i u) + (Q i u - R i u) + (R i u - V)‖
      ≤ ‖T - P i u‖ + ‖P i u - Q i u‖ +
          ‖Q i u - R i u‖ + ‖R i u - V‖ := by
            calc
              _ ≤ ‖(T - P i u) + (P i u - Q i u) + (Q i u - R i u)‖ +
                  ‖R i u - V‖ := norm_add_le _ _
              _ ≤ (‖(T - P i u) + (P i u - Q i u)‖ + ‖Q i u - R i u‖) +
                  ‖R i u - V‖ := by gcongr; exact norm_add_le _ _
              _ ≤ (‖T - P i u‖ + ‖P i u - Q i u‖ + ‖Q i u - R i u‖) +
                  ‖R i u - V‖ := by gcongr; exact norm_add_le _ _
              _ = _ := by ring
    _ ≤ Kpair * W.mcount i + Kcoef * W.mcount i +
          Kswitch * W.mcount i + Kread * W.mcount i := by
            have hp := hpair i u hu
            have hc := hcoef i u hu
            have hs := hswitch i u hu
            have hr := hread i u hu
            dsimp only [T, V] at *
            gcongr
    _ = _ := by ring

variable [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- The uniform version of the finite window conclusion. Its terminal comparison
is exactly the left side of `window_conversion_pieces.window_decay`; the constant
`Kwin` includes supported pair, coefficient, mass-switch and read charges. -/
theorem window_conversion_pieces_of_uniform
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)
    {Kconv Kwin : ℝ} {ε : ℕ → ℝ} (βs : ι → ℕ → ℝ)
    (analytic_T : ∀ i, ∀ n, sc i + 1 ≤ n → n ≤ k →
      AnalyticOnNhd ℂ (fun u => (W.chain i).T u n) S)
    (p7_first : ∀ i, ∀ n, sc i + 2 ≤ n → n ≤ k → ∀ u ∈ S,
      ‖(W.chain i).cost u n‖ ≤ Kconv *
        ((βs i (sc i + 1) * ε (sc i + 1) ^ 2) / (βs i n * ε n ^ 2)) * W.mcount i)
    (window_uniform : ∀ i, ∀ u ∈ S,
      ‖(W.chain i).T u k - (W.βk : ℂ) *
        actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)‖ ≤
          Kwin * W.mcount i)
    (analytic_win : ∀ i,
      AnalyticOnNhd ℂ (fun u => (W.βk : ℂ) *
        actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)) S)
    {γ η α α₀ : ℝ} (hd : 2 ≤ d) (hL : 1 < L) (hγ : 0 < γ) (hα₀ : 0 < α₀)
    (hε : ε = epsSeq L α α₀) (hγα : (d : ℝ) - 2 - 2 * α = 2 * γ)
    (hflow : ∀ i, ∃ B : ℝ, 0 < B ∧ ∃ g : ℕ → ℝ,
      (∀ m, Real.exp (-η) ≤ g m ∧ g m ≤ Real.exp η) ∧
      ∀ n, sc i + 1 ≤ n → n ≤ k → βs i n = B * (L : ℝ) ^ ((d - 2) * n) * g n)
    (hKc : 0 ≤ Kconv) (hKw : 0 ≤ Kwin) :
    ∃ C : U → ℂ,
      (∀ u ∈ S, (W.βk : ℂ) * actionRegionC W.Xwin W.ak W.νk
        (W.Datw u) (W.φw u) = ∑ i, (W.chain i).T u (sc i + 1) + C u) ∧
      AnalyticOnNhd ℂ C S ∧
      ∀ u ∈ S, ‖C u‖ ≤
        (9 * Real.exp (2 * η) * Kconv / (1 - (L : ℝ) ^ (-(2 * γ))) + Kwin) *
          ∑ i, W.mcount i := by
  apply window_conversion_pieces W (Kconv := Kconv) (Kbg := Kwin)
    (γw := 0) (M := 0) (M₁ := 0) (ε := ε) (Rhat := fun _ => 0)
    βs analytic_T p7_first
  · intro i u hu
    simpa using window_uniform i u hu
  · exact analytic_win
  · exact hd
  · exact hL
  · exact hγ
  · exact hα₀
  · exact hε
  · exact hγα
  · exact hflow
  · exact hKc
  · exact hKw
  · norm_num
  · intro i
    norm_num

/-- The complete finite window implication from an RG step envelope, the named
originating-piece regional source estimate, and the named uniform terminal comparison.
The source and terminal premises are the remaining physical estimates; all flow and
geometric-series arithmetic is discharged here. -/
theorem window_conversion_pieces_of_rg_source
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k)
    (βs : ι → ℕ → ℝ) (ξ : ι → ℕ → Fin 3 → ℝ)
    (β Cξ Ksrc Kwin α α₀ γ η : ℝ)
    (hβ : 0 < β) (hCξ : 0 ≤ Cξ) (hKsrc : 0 ≤ Ksrc) (hKwin : 0 ≤ Kwin)
    (hd : 2 ≤ d) (hL : 1 < L) (hγ : 0 < γ) (hα₀ : 0 < α₀)
    (hγα : (d : ℝ) - 2 - 2 * α = 2 * γ)
    (hrg : ∀ i, ∃ g : ℕ → ℝ,
      (∀ m, Real.exp (-η) ≤ g m ∧ g m ≤ Real.exp η) ∧
      ∀ m, βs i m = β * (L : ℝ) ^ ((d - 2) * m) * g m)
    (hξ : ∀ i t, ‖ξ i t‖ ≤ Cξ * β⁻¹ *
      ((L : ℝ) ^ (-(2 * γ))) ^ (t + 1))
    (hsource : ∀ i n, sc i + 2 ≤ n → n ≤ k → ∀ u ∈ S,
      ‖(W.chain i).cost u n‖ ≤
        Ksrc * (βs i (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2) *
          ‖ξ i (n - 1)‖ * W.mcount i)
    (analytic_T : ∀ i, ∀ n, sc i + 1 ≤ n → n ≤ k →
      AnalyticOnNhd ℂ (fun u => (W.chain i).T u n) S)
    (window_uniform : ∀ i, ∀ u ∈ S,
      ‖(W.chain i).T u k - (W.βk : ℂ) *
        actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)‖ ≤
          Kwin * W.mcount i)
    (analytic_win : ∀ i,
      AnalyticOnNhd ℂ (fun u => (W.βk : ℂ) *
        actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)) S) :
    ∃ C : U → ℂ,
      (∀ u ∈ S, (W.βk : ℂ) * actionRegionC W.Xwin W.ak W.νk
        (W.Datw u) (W.φw u) = ∑ i, (W.chain i).T u (sc i + 1) + C u) ∧
      AnalyticOnNhd ℂ C S ∧
      ∀ u ∈ S, ‖C u‖ ≤
        (9 * Real.exp (2 * η) *
            (9 * Ksrc * Cξ * α₀ ^ 2 * Real.exp η) /
            (1 - (L : ℝ) ^ (-(2 * γ))) + Kwin) *
          ∑ i, W.mcount i := by
  have hp7 := p7_first_of_rg_source W βs ξ β Cξ Ksrc α α₀ γ η
    hβ hCξ hKsrc hα₀ hL hd hγα hrg hξ hsource
  have hf : ∀ i, ∃ B : ℝ, 0 < B ∧ ∃ g : ℕ → ℝ,
      (∀ m, Real.exp (-η) ≤ g m ∧ g m ≤ Real.exp η) ∧
      ∀ n, sc i + 1 ≤ n → n ≤ k →
        βs i n = B * (L : ℝ) ^ ((d - 2) * n) * g n := by
    intro i
    obtain ⟨g, hg, hb⟩ := hrg i
    exact ⟨β, hβ, g, hg, fun n _ _ => hb n⟩
  have hKconv : 0 ≤ 9 * Ksrc * Cξ * α₀ ^ 2 * Real.exp η := by positivity
  exact window_conversion_pieces_of_uniform W βs analytic_T hp7 window_uniform
    analytic_win hd hL hγ hα₀ rfl hγα hf hKconv hKwin

end Balaban.LargeField.ActionConv
