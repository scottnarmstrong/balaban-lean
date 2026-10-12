/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Def5
public import Balaban.Background.MinimizerExpansion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cube action and its holomorphy (FLUCTUATION.md §4.2, Steps 1 and 3)

Step 3 of the proof of Theorem 4.2 partitions the restricted action into cubes `□` (P5 (1.5),
"counting half bonds on the star once") and studies the difference `F_□` of the cube action at the
two backgrounds `φ^loc + δφ` and `φ^loc`.

* `cubeActionR`, `cubeActionC`: the terms of the bilinear complex action `actionC`
  (`Background/MinimizerExpansion.lean`) supported at the sites of a finite set `Q`: the block term
  and the mass term at the sites of `Q ∩ Ω₁`, and the bond `{x, x + e_μ}` at its base site `x ∈ Q`
  (so that each bond is counted once);
* `cubeActionC_univ`: for `Q` the whole torus this is `actionC`;
* `cubeActionC_partition`: the cube actions of a partition of the torus add up to `actionC`;
* `cubeActionR_analyticAt`: `cubeActionR` is holomorphic in the action data and the field;
* `cubeDiff_analytic`: **holomorphy of `F_□`**: if the data of the action and of the two backgrounds
  depend analytically on a parameter `p` in an open set and lie in the complex domain `𝒟` of
  Theorem 5.2, then `p ↦ A_Q(φ(D_new)) - A_Q(φ(D_old))` is holomorphic (`theorem72_analytic`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Finset

section Def

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ)

/-- The block term of `actionC` at the site `x ∈ Ω₁`. -/
noncomputable def cubeBlockTerm (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ)
    (x : G.Ω 1) : ℂ :=
  ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
        ∑ i, (Ψ x i - blockAvg G φ x i) * (Ψ x i - blockAvg G φ x i)

/-- The bond term of `actionC` at the bonds `{x, x + e_μ}` based at the site `x`. -/
noncomputable def cubeBondTerm (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) : ℂ :=
  ∑ μ : Fin d, (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) *
          (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) else 0)

/-- The mass term of `actionC` at the site `x ∈ Ω₁`. -/
noncomputable def cubeMassTerm (h : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ)
    (x : G.Ω 1) : ℂ :=
  ∑ i, (φ (x, i) - h x i) * (φ (x, i) - h x i)

open Classical in
/-- **The bilinear action localized to a set `Q` of sites** (the cube action of FLUCTUATION
§4.2 Step 3 / P5 (1.5)): the terms of `actionC` supported at the sites of `Q`.  The block term and
the mass term at `x ∈ Q ∩ Ω₁`, and the bond `{x, x + e_μ}` at its base site `x ∈ Q`, so that every
bond is counted exactly once in a partition of the torus into cubes. -/
noncomputable def cubeActionR (Q : Finset (Torus d (N₀ * L ^ k)))
    (Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  (1 / 2) * ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeBlockTerm G a Ψ φ x else 0) +
  (1 / 2) * ∑ x : Torus d (N₀ * L ^ k), (if x ∈ Q then cubeBondTerm G Ψ φ x else 0) +
  (ν : ℂ) / 2 * ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeMassTerm G h φ x else 0)

/-- The cube action of the background data `D`. -/
noncomputable def cubeActionC (Q : Finset (Torus d (N₀ * L ^ k))) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  cubeActionR G a ν Q D.Ψ D.h φ

variable {G a ν}

/-- The cube action of the whole torus is the whole-lattice action `actionC`. -/
theorem cubeActionC_univ (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    cubeActionC G a ν Finset.univ D φ = actionC G a ν D φ := by
  unfold cubeActionC cubeActionR actionC cubeBlockTerm cubeBondTerm cubeMassTerm
  simp only [Finset.mem_univ, ↓reduceIte]

/-- **Partition of the action into cubes**: if the cubes `Q ∈ 𝒬` partition the torus, the cube
actions add up to the action. -/
theorem cubeActionC_partition (𝒬 : Finset (Finset (Torus d (N₀ * L ^ k))))
    (hpart : ∀ x, ∃! Q, Q ∈ 𝒬 ∧ x ∈ Q) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    ∑ Q ∈ 𝒬, cubeActionC G a ν Q D φ = actionC G a ν D φ := by
  classical
  have key : ∀ (x : Torus d (N₀ * L ^ k)) (t : ℂ),
      ∑ Q ∈ 𝒬, (if x ∈ Q then t else 0) = t := by
    intro x t
    obtain ⟨Q₀, ⟨hQ₀, hx⟩, hu⟩ := hpart x
    rw [Finset.sum_eq_single Q₀]
    · simp [hx]
    · intro Q hQ hne
      have : x ∉ Q := fun h => hne (hu Q ⟨hQ, h⟩)
      simp [this]
    · intro h; exact absurd hQ₀ h
  rw [← cubeActionC_univ]
  unfold cubeActionC cubeActionR
  simp only [Finset.mem_univ, ↓reduceIte, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  congr 1
  · congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => key _ _
  · congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => key _ _
  · congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => key _ _


end Def

section Analytic

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_svec {Φ : E → G.Ω 1 × Fin N → ℂ} {p : E} (hΦ : AnalyticAt ℂ Φ p)
    (y : Torus d (N₀ * L ^ k)) (i : Fin N) : AnalyticAt ℂ (fun q => svec G (Φ q) y i) p := by
  classical
  by_cases hy : y ∈ G.Ω 1
  · have : (fun q => svec G (Φ q) y i) = fun q => Φ q (⟨y, hy⟩, i) := by
      funext q; exact svec_of_mem G (Φ q) ⟨y, hy⟩ i
    rw [this]
    exact analyticAt_pi_iff.1 hΦ _
  · have : (fun q => svec G (Φ q) y i) = fun _ => 0 := by
      funext q; exact svec_of_not_mem G (Φ q) hy i
    rw [this]
    exact analyticAt_const

theorem analyticAt_blockAvg {Φ : E → G.Ω 1 × Fin N → ℂ} {p : E} (hΦ : AnalyticAt ℂ Φ p)
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) : AnalyticAt ℂ (fun q => blockAvg G (Φ q) x i) p := by
  unfold blockAvg
  have := fun y => analyticAt_svec hΦ y i
  fun_prop

theorem analyticAt_barField {Ψ : E → Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {Φ : E → G.Ω 1 × Fin N → ℂ} {p : E} (hΨ : AnalyticAt ℂ Ψ p) (hΦ : AnalyticAt ℂ Φ p)
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    AnalyticAt ℂ (fun q => barField G (Ψ q) (Φ q) x i) p := by
  classical
  by_cases hx : x ∈ G.Ω 1
  · have : (fun q => barField G (Ψ q) (Φ q) x i) = fun q => Φ q (⟨x, hx⟩, i) := by
      funext q; simp [barField, hx]
    rw [this]; exact analyticAt_pi_iff.1 hΦ _
  · have : (fun q => barField G (Ψ q) (Φ q) x i) = fun q => Ψ q x i := by
      funext q; simp [barField, hx]
    rw [this]; exact analyticAt_pi_iff.1 (analyticAt_pi_iff.1 hΨ x) i

/-- **Holomorphy of the cube action**: if the action data `(Ψ, h)` and the field `φ` depend
analytically on a parameter `p`, so does `cubeActionR`. -/
theorem cubeActionR_analyticAt (Q : Finset (Torus d (N₀ * L ^ k)))
    {Ψ h : E → Torus d (N₀ * L ^ k) → Fin N → ℂ} {Φ : E → G.Ω 1 × Fin N → ℂ} {p : E}
    (hΨ : AnalyticAt ℂ Ψ p) (hh : AnalyticAt ℂ h p) (hΦ : AnalyticAt ℂ Φ p) :
    AnalyticAt ℂ (fun q => cubeActionR G a ν Q (Ψ q) (h q) (Φ q)) p := by
  classical
  have c1 : ∀ x i, AnalyticAt ℂ (fun q => Ψ q x i) p :=
    fun x i => analyticAt_pi_iff.1 (analyticAt_pi_iff.1 hΨ x) i
  have c2 : ∀ x i, AnalyticAt ℂ (fun q => h q x i) p :=
    fun x i => analyticAt_pi_iff.1 (analyticAt_pi_iff.1 hh x) i
  have c3 : ∀ z i, AnalyticAt ℂ (fun q => Φ q (z, i)) p :=
    fun z i => analyticAt_pi_iff.1 hΦ (z, i)
  have c4 := fun x i => analyticAt_blockAvg hΦ x i
  have c5 := fun x i => analyticAt_barField hΨ hΦ x i
  unfold cubeActionR cubeBlockTerm cubeBondTerm cubeMassTerm
  refine AnalyticAt.add (AnalyticAt.add ?_ ?_) ?_
  · refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ => ?_)
    by_cases hx : (x : Torus d (N₀ * L ^ k)) ∈ Q
    · simp only [hx, ↓reduceIte]
      exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun i _ => by
        have := c1 x i; have := c4 x i; fun_prop)
    · simp only [hx, ↓reduceIte]; exact analyticAt_const
  · refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ => ?_)
    by_cases hx : x ∈ Q
    · simp only [hx, ↓reduceIte]
      refine Finset.analyticAt_fun_sum _ fun μ _ => ?_
      by_cases hμ : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
      · simp only [hμ, ↓reduceIte]
        exact Finset.analyticAt_fun_sum _ fun i _ => by
          have := c5 x i; have := c5 (x + Pi.single μ 1) i; fun_prop
      · simp only [hμ, ↓reduceIte]; exact analyticAt_const
    · simp only [hx, ↓reduceIte]; exact analyticAt_const
  · refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ => ?_)
    by_cases hx : (x : Torus d (N₀ * L ^ k)) ∈ Q
    · simp only [hx, ↓reduceIte]
      exact Finset.analyticAt_fun_sum _ fun i _ => by
        have := c3 x i; have := c2 x i; fun_prop
    · simp only [hx, ↓reduceIte]; exact analyticAt_const


/-- **Holomorphy of the cube action difference.**  Let `s` be an open set of parameters `p` of a
complex normed space (the complex data), `Dact p` the data of the action and `Dold p`, `Dnew p`
the data of the two backgrounds, depending analytically on `p ∈ s` and lying in the complex domain
`𝒟` of Theorem 5.2.  Then
`p ↦ A_Q(Dact p; φ(Dnew p)) - A_Q(Dact p; φ(Dold p))`, `φ = bgFieldC`, is holomorphic on `s`. -/
theorem cubeDiff_analytic (H : BgHyp d L k ϱ a ν) (Q : Finset (Torus d (N₀ * L ^ k)))
    {s : Set E} (hs : IsOpen s) (Dact Dold Dnew : E → BgData G N)
    (hact : AnalyticOnNhd ℂ (fun p => ((Dact p).Ψ, (Dact p).h)) s)
    (hold : AnalyticOnNhd ℂ (fun p => ((Dold p).Ψ, (Dold p).h)) s)
    (hnew : AnalyticOnNhd ℂ (fun p => ((Dnew p).Ψ, (Dnew p).h)) s)
    (hdold : ∀ p ∈ s, InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (Dold p))
    (hdnew : ∀ p ∈ s, InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (Dnew p)) :
    AnalyticOnNhd ℂ (fun p => cubeActionC G a ν Q (Dact p) (bgFieldC G a ν (bgC0 d L N) (Dnew p)) -
      cubeActionC G a ν Q (Dact p) (bgFieldC G a ν (bgC0 d L N) (Dold p))) s := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := G) (a := a) (ν := ν) H
  have hΦ : ∀ (Dd : E → BgData G N),
      AnalyticOnNhd ℂ (fun p => ((Dd p).Ψ, (Dd p).h)) s →
      (∀ p ∈ s, InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (Dd p)) →
      AnalyticOnNhd ℂ (fun p => bgFieldC G a ν (bgC0 d L N) (Dd p)) s := by
    intro Dd hD hdd
    have h1 : AnalyticOnNhd ℂ (fun p => (F ((Dd p).Ψ, (Dd p).h)).1) s := fun p hp =>
      analyticAt_fst.comp (AnalyticAt.comp (hF _ ⟨Dd p, hdd p hp, rfl⟩) (hD p hp))
    refine h1.congr hs fun p hp => ?_
    show (F ((Dd p).Ψ, (Dd p).h)).1 = bgFieldC G a ν (bgC0 d L N) (Dd p)
    rw [hFe (Dd p) (hdd p hp)]
  have hA : ∀ (Dd : E → BgData G N),
      AnalyticOnNhd ℂ (fun p => ((Dd p).Ψ, (Dd p).h)) s →
      ∀ p ∈ s, AnalyticAt ℂ (fun q => (Dd q).Ψ) p ∧ AnalyticAt ℂ (fun q => (Dd q).h) p := by
    intro Dd hD p hp
    exact ⟨analyticAt_fst.comp (hD p hp), analyticAt_snd.comp (hD p hp)⟩
  intro p hp
  obtain ⟨h1, h2⟩ := hA Dact hact p hp
  exact (cubeActionR_analyticAt Q h1 h2 (hΦ Dnew hnew hdnew p hp)).sub
    (cubeActionR_analyticAt Q h1 h2 (hΦ Dold hold hdold p hp))

end Analytic

end Balaban.Fluctuation
