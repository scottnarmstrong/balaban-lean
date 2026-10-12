/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CubeAction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cube action in the star convention (FLUCTUATION.md §4.2 Step 3, P5 (1.5))

`CubeAction.lean` charges every bond `{x, x + e_μ}` to its base site `x`.  The localized action of
the large-field step (Definition II.5.4, `mainActionLoc`) is
`A_𝔹(X; ψ, φ) + ¼ ∑_{b ∈ st(X)} |∂φ(b)|²`: bonds inside `X` count with weight `½`, the boundary
(star) bonds with weight `¼`.  Per cube the two conventions differ by the bonds leaving the cube;
only the star convention gives the cube actions of a partition of `X` adding up to the localized
action of `X`.

* `starWeight Q x μ`: `1` (both ends in `Q`), `½` (one end), `0`;
* `cubeActionStar`: the terms of `actionC` supported at `Q`, bond `{x, x+e_μ}` weighted by
  `½ · starWeight`;
* `cubeActionStar_univ`: for `Q` the whole torus this is `actionC`;
* `cubeActionStar_partition`: the star actions of the cubes of a partition of `X` add up to the
  star action of `X`;
* `cubeActionStar_analyticAt`: holomorphy in the data and the field.
-/


@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Finset

section Def

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ)

open Classical in
/-- The weight of the bond `{x, x + e_μ}` in the cube action of `Q` with the star convention:
`1` if both end points lie in `Q`, `1/2` if exactly one does, `0` if none. -/
noncomputable def starWeight (Q : Finset (Torus d (N₀ * L ^ k))) (x : Torus d (N₀ * L ^ k))
    (μ : Fin d) : ℂ :=
  ((if x ∈ Q then 1 else 0) + (if x + Pi.single μ 1 ∈ Q then 1 else 0)) / 2

/-- The bond term of `actionC` at the bonds `{x, x + e_μ}` based at `x`, weighted by the star
convention. -/
noncomputable def cubeBondStar (Q : Finset (Torus d (N₀ * L ^ k)))
    (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) : ℂ :=
  ∑ μ : Fin d, (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then starWeight Q x μ *
        ∑ i, (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) *
          (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) else 0)

open Classical in
/-- **The cube action in the star convention** (P5 (1.5), "half bonds on the star counted once"):
the block and mass terms at the sites of `Q ∩ Ω₁`, the bonds with both end points in `Q` with
weight `1/2` and the bonds with exactly one end point in `Q` with weight `1/4`. -/
noncomputable def cubeActionStar (Q : Finset (Torus d (N₀ * L ^ k)))
    (Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  (1 / 2) * ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeBlockTerm G a Ψ φ x else 0) +
  (1 / 2) * ∑ x : Torus d (N₀ * L ^ k), cubeBondStar G Q Ψ φ x +
  (ν : ℂ) / 2 * ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Q then cubeMassTerm G h φ x else 0)

variable {G a ν}

theorem starWeight_univ (x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    starWeight (Finset.univ : Finset (Torus d (N₀ * L ^ k))) x μ = 1 := by
  unfold starWeight; simp

/-- For `Q` the whole torus this is the whole-lattice action `actionC`. -/
theorem cubeActionStar_univ (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    cubeActionStar G a ν Finset.univ D.Ψ D.h φ = actionC G a ν D φ := by
  unfold cubeActionStar actionC cubeBlockTerm cubeBondStar cubeMassTerm
  simp only [Finset.mem_univ, ↓reduceIte, starWeight_univ, one_mul]

/-- **Partition of the star action into cubes**: if the cubes `Q b`, `b ∈ 𝒬`, partition `X`, the
star actions of the cubes add up to the star action of `X`. -/
theorem cubeActionStar_partition {B : Type*} (𝒬 : Finset B)
    (Q : B → Finset (Torus d (N₀ * L ^ k))) (X : Finset (Torus d (N₀ * L ^ k)))
    (hsub : ∀ b ∈ 𝒬, Q b ⊆ X) (hpart : ∀ x ∈ X, ∃! b, b ∈ 𝒬 ∧ x ∈ Q b)
    (Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ) :
    ∑ b ∈ 𝒬, cubeActionStar G a ν (Q b) Ψ h φ = cubeActionStar G a ν X Ψ h φ := by
  classical
  have key2 : ∀ (x : Torus d (N₀ * L ^ k)) (t : ℂ),
      ∑ b ∈ 𝒬, (if x ∈ Q b then t else 0) = if x ∈ X then t else 0 := by
    intro x t
    by_cases hx : x ∈ X
    · obtain ⟨b₀, ⟨hb₀, hxb⟩, hu⟩ := hpart x hx
      rw [Finset.sum_eq_single b₀]
      · simp [hxb, hx]
      · intro b hb hne
        have : x ∉ Q b := fun h => hne (hu b ⟨hb, h⟩)
        simp [this]
      · intro h; exact absurd hb₀ h
    · simp only [hx, ↓reduceIte]
      refine Finset.sum_eq_zero fun b hb => ?_
      have : x ∉ Q b := fun h => hx (hsub b hb h)
      simp [this]
  have key : ∀ (x : Torus d (N₀ * L ^ k)),
      ∑ b ∈ 𝒬, ((if x ∈ Q b then 1 else 0 : ℂ)) = if x ∈ X then 1 else 0 := fun x => key2 x 1
  unfold cubeActionStar
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  congr 1
  · congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => key2 _ _
  · congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold cubeBondStar
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    unfold starWeight
    by_cases hμ : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
    · simp only [hμ, ↓reduceIte]
      simp only [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib, key]
    · simp [hμ]
  · congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => key2 _ _

/-- **The left side of (4.2) for the real step**: for cubes partitioning `X`,
`∑_□ β F_□ = β (A_X(φ') - A_X(φ))` in the star convention. -/
theorem sum_cubeDiffStar_eq {B : Type*} (𝒬 : Finset B) (Q : B → Finset (Torus d (N₀ * L ^ k)))
    (X : Finset (Torus d (N₀ * L ^ k))) (hsub : ∀ b ∈ 𝒬, Q b ⊆ X)
    (hpart : ∀ x ∈ X, ∃! b, b ∈ 𝒬 ∧ x ∈ Q b) (D : BgData G N) (φ φ' : G.Ω 1 × Fin N → ℂ)
    (β : ℂ) :
    ∑ b ∈ 𝒬, β * (cubeActionStar G a ν (Q b) D.Ψ D.h φ' - cubeActionStar G a ν (Q b) D.Ψ D.h φ) =
      β * (cubeActionStar G a ν X D.Ψ D.h φ' - cubeActionStar G a ν X D.Ψ D.h φ) := by
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, cubeActionStar_partition 𝒬 Q X hsub hpart,
    cubeActionStar_partition 𝒬 Q X hsub hpart]

end Def

section Analytic

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Holomorphy of the star cube action** in the action data and the field. -/
theorem cubeActionStar_analyticAt (Q : Finset (Torus d (N₀ * L ^ k)))
    {Ψ h : E → Torus d (N₀ * L ^ k) → Fin N → ℂ} {Φ : E → G.Ω 1 × Fin N → ℂ} {p : E}
    (hΨ : AnalyticAt ℂ Ψ p) (hh : AnalyticAt ℂ h p) (hΦ : AnalyticAt ℂ Φ p) :
    AnalyticAt ℂ (fun q => cubeActionStar G a ν Q (Ψ q) (h q) (Φ q)) p := by
  classical
  have c1 : ∀ x i, AnalyticAt ℂ (fun q => Ψ q x i) p :=
    fun x i => analyticAt_pi_iff.1 (analyticAt_pi_iff.1 hΨ x) i
  have c2 : ∀ x i, AnalyticAt ℂ (fun q => h q x i) p :=
    fun x i => analyticAt_pi_iff.1 (analyticAt_pi_iff.1 hh x) i
  have c3 : ∀ z i, AnalyticAt ℂ (fun q => Φ q (z, i)) p :=
    fun z i => analyticAt_pi_iff.1 hΦ (z, i)
  have c4 := fun x i => analyticAt_blockAvg hΦ x i
  have c5 := fun x i => analyticAt_barField hΨ hΦ x i
  unfold cubeActionStar cubeBlockTerm cubeBondStar cubeMassTerm
  refine AnalyticAt.add (AnalyticAt.add ?_ ?_) ?_
  · refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ => ?_)
    by_cases hx : (x : Torus d (N₀ * L ^ k)) ∈ Q
    · simp only [hx, ↓reduceIte]
      exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun i _ => by
        have := c1 x i; have := c4 x i; fun_prop)
    · simp only [hx, ↓reduceIte]; exact analyticAt_const
  · refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ => ?_)
    refine Finset.analyticAt_fun_sum _ fun μ _ => ?_
    by_cases hμ : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
    · simp only [hμ, ↓reduceIte]
      refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun i _ => ?_)
      have := c5 x i; have := c5 (x + Pi.single μ 1) i; fun_prop
    · simp only [hμ, ↓reduceIte]; exact analyticAt_const
  · refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ => ?_)
    by_cases hx : (x : Torus d (N₀ * L ^ k)) ∈ Q
    · simp only [hx, ↓reduceIte]
      exact Finset.analyticAt_fun_sum _ fun i _ => by
        have := c3 x i; have := c2 x i; fun_prop
    · simp only [hx, ↓reduceIte]; exact analyticAt_const

end Analytic

end Balaban.Fluctuation
