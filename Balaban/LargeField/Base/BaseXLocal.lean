/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseXSqrt
public import Balaban.Localization.DecoupledCovClose
public import Balaban.Localization.Decoupled2FpGeometry
public import Balaban.Localization.DecoupledCovLocal

/-!
# Locality of the first step's shifted covariance and of its square root

Weighted comparison and exact core agreement of the shifted covariance
`(1 + x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` of the first step, uniformly in `x ≥ 0`, and of its Stieltjes
square root `π⁻¹ ∫₀^∞ x^{-1/2} C_x(s) dx`.  Everything is an application of the landed locality
and closeness theorems of the step's x-variant chain at `x' = 0` and mass `ν + x`.

* `baseCovX_sub_decay`: two parameter families equal to `1` off `W` give covariances whose entries
  differ by `B e^{-γ r(y)}`, `r` the truncated distance from `y` to `W`, uniformly in `x ≥ 0`
  (from `vecM_decZ_sub_le_cover`).
* `baseCovX_exact`: if every active cube lies inside `Sr` or is disjoint from `Y ⊇ Sr`, the
  parameters agree on the cubes inside `Sr`, and `Y` contains the neighbours of `Sr`, then the rows
  of the covariance at the sites of `Y` do not depend on `s` (from `Gsx_local`, the fixed point
  of `decZ_exact`).
* `baseCovX_sqrt_sub_decay`, `baseCovX_sqrt_exact`: the same for the Stieltjes square root; the
  weighted comparison loses half the rate (`stieltjes_interp`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Matrix

section Entry

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- An entry of an operator that is bounded in the weighted block norm decays with the weight. -/
theorem entry_sq_mul_le_of_vecM (M : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) {K ε : ℝ}
    (r : Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℝ) (hK : 0 ≤ K)
    (h : ∀ f : G.Ω 1 × Fin N → ℂ, vecM G ε r (M *ᵥ f) ≤ K * vecSrc G 0 (fun _ => 0) f)
    (y z : G.Ω 1 × Fin N) :
    ‖M y z‖ ^ 2 * Real.exp (ε * r y.1) ^ 2 ≤ K * (((L : ℝ) ^ (k + 1)) ^ 2) ^ 2 := by
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h1 := h (Pi.single z 1)
  have h2 := (sqNorm_le_vecSrc_zero (N := N) (H := G) hL1 (Pi.single z 1 : G.Ω 1 × Fin N → ℂ)).2
  rw [sqNorm_single] at h2
  set u : G.Ω 1 × Fin N → ℂ := M *ᵥ (Pi.single z 1 : G.Ω 1 × Fin N → ℂ) with hu
  have hent : u y = M y z := mulVec_single_entry M y z
  have hsp := spacing_pos (G := G) (x := y.1)
  have hspl := spacing_le (G := G) y.1.2
  have hv : ‖u y‖ ^ 2 ≤ vn (svec G u y.1) ^ 2 := by
    rw [vn_sq]
    have := Finset.single_le_sum (f := fun i => ‖svec G u y.1 i‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ y.2)
    refine le_trans (le_of_eq ?_) this
    simp only [svec]
    rw [zeroExt_mem' _ y.1.2]
  have hw : invSqSpacing G y.1 * (Real.exp (ε * r y.1) * vn (svec G u y.1)) ^ 2 ≤ vecM G ε r u := by
    unfold vecM wsq
    exact Finset.single_le_sum (f := fun x => invSqSpacing G x *
      (Real.exp (ε * r x) * vn (svec G u x)) ^ 2)
      (fun x _ => mul_nonneg (invSqSpacing_nonneg G x) (sq_nonneg _)) (Finset.mem_univ (y.1 : Torus d (N₁ * L ^ m₁ * L ^ (k + 1))))
  rw [invSqSpacing_eq G y.1.2] at hw
  have hsq : 0 < G.spacing y.1 ^ 2 := by positivity
  have h3 : ‖u y‖ ^ 2 * Real.exp (ε * r y.1) ^ 2 ≤
      G.spacing y.1 ^ 2 * (K * (((L : ℝ) ^ (k + 1)) ^ 2)) := by
    have e1 : ‖u y‖ ^ 2 * Real.exp (ε * r y.1) ^ 2 ≤
        (Real.exp (ε * r y.1) * vn (svec G u y.1)) ^ 2 := by
      rw [mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_left hv (sq_nonneg _)
    have e2 : (Real.exp (ε * r y.1) * vn (svec G u y.1)) ^ 2 ≤
        G.spacing y.1 ^ 2 * (K * (((L : ℝ) ^ (k + 1)) ^ 2)) := by
      have := hw.trans (h1.trans (mul_le_mul_of_nonneg_left h2 hK))
      rw [mul_one] at this
      rw [inv_mul_le_iff₀ hsq] at this
      exact this
    exact e1.trans e2
  rw [hent] at h3
  refine h3.trans ?_
  have : G.spacing y.1 ^ 2 ≤ ((L : ℝ) ^ (k + 1)) ^ 2 := pow_le_pow_left₀ hsp.le hspl 2
  calc _ ≤ ((L : ℝ) ^ (k + 1)) ^ 2 * (K * (((L : ℝ) ^ (k + 1)) ^ 2)) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = _ := by ring

end Entry

section Compare

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx x : ℝ}

theorem zCloseConst_nonneg (d L : ℕ) : 0 ≤ zCloseConst d L := by
  unfold zCloseConst closeConstX gradCloseConstX gradStarConstX valConstX
  have := commXConst_nonneg d L
  positivity

/-- The weighted closeness of `Z_s = Ĝ_{0,s} - Π_{0,s}` (at mass `ν + x`) to `Z_1`, entrywise. -/
theorem decZ_sub_one_entry {κ δ : ℝ} {α : G.Ω 1 → ℂ}
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    (S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx) (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hα : AdmPot G α)
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {W : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)}
    (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (hφ : IsConstraintField G δ φ)
    (T : ℝ) (y z : G.Ω 1 × Fin N) :
    ‖(decZ G a aT 0 (ν + x) α s φ - decZ G a aT 0 (ν + x) α (fun _ => 1) φ) y z‖ ≤
      Real.sqrt (zCloseConst d L * Real.exp (N0 d L * κ) ^ 2) * ((L : ℝ) ^ 2) *
        Real.exp (-(xAgmonRate d L * truncSetDistR G W T y.1)) := by
  have D : Dec2.XData (coverOf G) G a aT (ν + x) 0 α κ s Cx := ⟨S, hCx, hα, le_rfl, hκ, hM, hs⟩
  have hd : 0 < d := by have := S.hd; omega
  have hε0 : 0 ≤ xAgmonRate d L := (xAgmonRate_pos hd S.hL).le
  have hK : 0 ≤ zCloseConst d L * Real.exp (N0 d L * κ) ^ 2 :=
    mul_nonneg (zCloseConst_nonneg d L) (sq_nonneg _)
  have h := entry_sq_mul_le_of_vecM (G := G) (N := N)
    (decZ G a aT 0 (ν + x) α s φ - decZ G a aT 0 (ν + x) α (fun _ => 1) φ) (ε := xAgmonRate d L)
    (truncSetDistR G W T) hK
    (fun f => vecM_decZ_sub_le_cover D hW T hε0 le_rfl hφ hδ hsm f) y z
  set E := Real.exp (xAgmonRate d L * truncSetDistR G W T y.1) with hE
  have hEp : 0 < E := Real.exp_pos _
  have hneg : Real.exp (-(xAgmonRate d L * truncSetDistR G W T y.1)) = E⁻¹ := Real.exp_neg _
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h2 : (‖(decZ G a aT 0 (ν + x) α s φ - decZ G a aT 0 (ν + x) α (fun _ => 1) φ) y z‖ * E) ^ 2 ≤
      (Real.sqrt (zCloseConst d L * Real.exp (N0 d L * κ) ^ 2) * ((L : ℝ) ^ 2)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hK]
    calc _ = ‖(decZ G a aT 0 (ν + x) α s φ - decZ G a aT 0 (ν + x) α (fun _ => 1) φ) y z‖ ^ 2 *
          E ^ 2 := by ring
      _ ≤ _ := h
      _ = _ := by ring
  have h3 := abs_le_of_sq_le_sq' h2 (by positivity)
  have h4 := h3.2
  have key : ‖(decZ G a aT 0 (ν + x) α s φ - decZ G a aT 0 (ν + x) α (fun _ => 1) φ) y z‖ ≤
      Real.sqrt (zCloseConst d L * Real.exp (N0 d L * κ) ^ 2) * ((L : ℝ) ^ 2) * E⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hEp]
    exact h4
  calc _ ≤ _ := key
    _ = _ := by rw [hneg]

/-- The shifted covariance is `(1 + x)⁻¹ P_e` plus `Z`. -/
theorem baseCovX_eq_add_decZ {α : G.Ω 1 → ℂ} {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} :
    ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
        liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
        Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) =
      (1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) + decZ G a aT 0 (ν + x) α s φ :=
  add_sub_assoc _ _ _

/-- **Weighted comparison of the shifted covariance, uniformly in `x ≥ 0`.**  If two parameter
families `s`, `s'` on the discs `‖s_P‖ ≤ e^κ` are `1` on every cube whose interaction cube is not
inside `W`, the entries of the shifted covariance `(1 + x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` differ by
`B e^{-γ r(y)}`, `r` the path distance from `y` to `W` truncated at any `T`, `γ = xAgmonRate d L`.
The constant `B` depends only on `d, L, κ`; the bound is uniform in `x ≥ 0`, `ν`, `a`, `aT`, `G`. -/
theorem baseCovX_sub_decay {κ δ : ℝ} {α : G.Ω 1 → ℂ}
    {s s' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    (S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx) (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hα : AdmPot G α)
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {W : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)}
    (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W)
    (hW' : ∀ z ∈ cubeIdx G, sProd G s' z ≠ 1 → intBox z ⊆ W)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (hφ : IsConstraintField G δ φ)
    (T : ℝ) (y z : G.Ω 1 × Fin N) :
    ‖((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z -
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s') -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s' φ) y z‖ ≤
      2 * (Real.sqrt (zCloseConst d L * Real.exp (N0 d L * κ) ^ 2) * ((L : ℝ) ^ 2)) *
        Real.exp (-(xAgmonRate d L * truncSetDistR G W T y.1)) := by
  rw [baseCovX_eq_add_decZ, baseCovX_eq_add_decZ]
  have h1 := decZ_sub_one_entry S hCx hκ hM hδ hsm hα hs hW hφ T y z
  have h2 := decZ_sub_one_entry S hCx hκ hM hδ hsm hα hs' hW' hφ T y z
  have e : ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) + decZ G a aT 0 (ν + x) α s φ) y z -
      ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) + decZ G a aT 0 (ν + x) α s' φ) y z =
      (decZ G a aT 0 (ν + x) α s φ - decZ G a aT 0 (ν + x) α (fun _ => 1) φ) y z -
        (decZ G a aT 0 (ν + x) α s' φ - decZ G a aT 0 (ν + x) α (fun _ => 1) φ) y z := by
    simp only [Matrix.add_apply, Matrix.sub_apply]; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  linarith

end Compare

section Exact

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x₀ ν Cx κ δ : ℝ}
  {α : G.Ω 1 → ℂ} {s s' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ : Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {Sr Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}

/-- Outside every active cube the Green function vanishes. -/
theorem Gsx_mulVec_eq_zero_of_dich (u : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ)
    (hact : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd u q ≠ 0 →
      SubI G (intBox q) Sr ∨ DisjI G (intBox q) Y)
    (g : G.Ω 1 → ℂ) {y : G.Ω 1}
    (hyS : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∉ Sr)
    (hyY : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y) :
    (Dec2.Gsx (coverOf G) G a aT x₀ ν α u *ᵥ g) y = 0 := by
  classical
  have hcore : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∉ Dec2.Core (coverOf G) u := by
    intro h
    unfold Dec2.Core at h
    obtain ⟨q, hq, hyq⟩ := Finset.mem_biUnion.1 h
    have hq' := Finset.mem_filter.1 hq
    have hbox := coreBox_subset_box hyq
    rcases hact q hq'.1 hq'.2 with h1 | h1
    · exact hyS (h1 y hbox)
    · exact h1 y hbox hyY
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_eq_zero fun y' _ => by
    rw [Dec2.Gsx_apply_eq_zero_of_not_core (Dec2.footLocalGeom_coverOf G) y y' hcore, zero_mul]

/-- **Exact agreement of the Green function.**  If every active cube lies inside `Sr` or is
disjoint from `Y ⊇ Sr`, the parameters agree on the cubes inside `Sr`, and the sources agree on
`Sr`, then the outputs agree on all of `Y`. -/
theorem Gsx_exact (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hx : 0 ≤ x₀) (hα : AdmPot G α)
    (hU : IsUnit (1 - Dec2.Kcalx (coverOf G) G a aT x₀ ν α s))
    (hU' : IsUnit (1 - Dec2.Kcalx (coverOf G) G a aT x₀ ν α s'))
    (hdich : ∀ q ∈ (coverOf G).cubeIdx, ((coverOf G).sProd s q ≠ 0 ∨ (coverOf G).sProd s' q ≠ 0) →
      SubI G (intBox q) Sr ∨ DisjI G (intBox q) Y)
    (hSY : Sr ⊆ Y)
    (hagree : ∀ q ∈ (coverOf G).cubeIdx, SubI G (intBox q) Sr →
      (coverOf G).sProd s q = (coverOf G).sProd s' q)
    {g g' : G.Ω 1 → ℂ}
    (hg : ∀ y : G.Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr → g y = g' y) :
    ∀ y : G.Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y →
      (Dec2.Gsx (coverOf G) G a aT x₀ ν α s *ᵥ g) y =
        (Dec2.Gsx (coverOf G) G a aT x₀ ν α s' *ᵥ g') y := by
  classical
  intro y hyY
  by_cases hyS : (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr
  · refine Dec2.Gsx_local S hx hα hα hU hU' ?_ hagree (fun _ _ => rfl) hg y hyS
    intro q hq hact
    rcases hdich q hq hact with h | h
    · exact Or.inl h
    · exact Or.inr (fun x hx hxS => h x hx (hSY hxS))
  · rw [Gsx_mulVec_eq_zero_of_dich s (fun q hq h => hdich q hq (Or.inl h)) g hyS hyY,
      Gsx_mulVec_eq_zero_of_dich s' (fun q hq h => hdich q hq (Or.inr h)) g' hyS hyY]

section ZExact

variable (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hx : 0 ≤ x₀) (hα : AdmPot G α)
  (hU : IsUnit (1 - Dec2.Kcalx (coverOf G) G a aT x₀ ν α s))
  (hU' : IsUnit (1 - Dec2.Kcalx (coverOf G) G a aT x₀ ν α s'))
  (hdich : ∀ q ∈ (coverOf G).cubeIdx, ((coverOf G).sProd s q ≠ 0 ∨ (coverOf G).sProd s' q ≠ 0) →
    SubI G (intBox q) Sr ∨ DisjI G (intBox q) Y)
  (hSY : Sr ⊆ Y)
  (hagree : ∀ q ∈ (coverOf G).cubeIdx, SubI G (intBox q) Sr →
    (coverOf G).sProd s q = (coverOf G).sProd s' q)
  (hrow : ∀ z y : G.Ω 1, (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr →
    xDirichletOperator G a aT x₀ ν α z y ≠ 0 →
    (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y)
include S hx hα hU hU' hdich hSY hagree hrow

theorem commK_Gsx_exact {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr → ∀ i,
      w (y, i) = w' (y, i))
    {z : G.Ω 1} (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr) :
    (commK (xDirichletOperator G a aT x₀ ν α) (restrictField G φ) *ᵥ
        (liftOp N (Gsx G a aT x₀ ν α s) *ᵥ w)) z =
      (commK (xDirichletOperator G a aT x₀ ν α) (restrictField G φ) *ᵥ
        (liftOp N (Gsx G a aT x₀ ν α s') *ᵥ w')) z := by
  refine commK_apply_eq (fun y hy i => ?_)
  rw [liftOp_mulVec, liftOp_mulVec]
  exact Gsx_exact S hx hα hU hU' hdich hSY hagree (g := fun b => w (b, i))
    (g' := fun b => w' (b, i)) (fun b hb => hw b hb i) y (hrow z y hz hy)

theorem decN_exact {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr → ∀ i,
      w (y, i) = w' (y, i))
    {z : G.Ω 1} (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr) :
    (decN G a aT x₀ ν α s φ *ᵥ w) z = (decN G a aT x₀ ν α s' φ *ᵥ w') z := by
  rw [decN_mulVec_eq, decN_mulVec_eq, Pi.sub_apply, Pi.sub_apply]
  have e1 : ((fieldMul (restrictField G φ))ᵀ *ᵥ w) z =
      ((fieldMul (restrictField G φ))ᵀ *ᵥ w') z := by
    rw [fieldMul_transpose_mulVec, fieldMul_transpose_mulVec]
    exact Finset.sum_congr rfl fun i _ => by rw [hw z hz i]
  rw [e1, commK_Gsx_exact (φ := φ) S hx hα hU hU' hdich hSY hagree hrow hw hz]

theorem decM_exact {v v' : G.Ω 1 → ℂ}
    (hv : ∀ y : G.Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr → v y = v' y)
    {z : G.Ω 1} (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr) :
    (decM G a aT x₀ ν α s φ *ᵥ v) z = (decM G a aT x₀ ν α s' φ *ᵥ v') z := by
  rw [decM_mulVec_eq, decM_mulVec_eq, Pi.sub_apply, Pi.sub_apply]
  have e1 : ((fieldMul (restrictField G φ))ᵀ *ᵥ (fieldMul (restrictField G φ) *ᵥ v)) z =
      ((fieldMul (restrictField G φ))ᵀ *ᵥ (fieldMul (restrictField G φ) *ᵥ v')) z := by
    rw [fieldMul_transpose_mulVec, fieldMul_transpose_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fieldMul_mulVec, fieldMul_mulVec, hv z hz]
  have e2 := commK_Gsx_exact (φ := φ) S hx hα hU hU' hdich hSY hagree hrow
    (w := fieldMul (restrictField G φ) *ᵥ v) (w' := fieldMul (restrictField G φ) *ᵥ v')
    (fun y hy i => by rw [fieldMul_mulVec, fieldMul_mulVec, hv y hy]) hz
  rw [e1, e2]

omit hrow in
theorem Gvec_exact {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr → ∀ i,
      w (y, i) = w' (y, i)) :
    ∀ y : G.Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i,
      (liftOp N (Gsx G a aT x₀ ν α s) *ᵥ w) (y, i) =
        (liftOp N (Gsx G a aT x₀ ν α s') *ᵥ w') (y, i) := by
  intro y hy i
  rw [liftOp_mulVec, liftOp_mulVec]
  exact Gsx_exact S hx hα hU hU' hdich hSY hagree (g := fun b => w (b, i))
    (g' := fun b => w' (b, i)) (fun b hb => hw b hb i) y hy

end ZExact

section ZExact2

variable (D : Dec2.XData (coverOf G) G a aT ν x₀ α κ s Cx)
  (D' : Dec2.XData (coverOf G) G a aT ν x₀ α κ s' Cx)
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hdich : ∀ q ∈ (coverOf G).cubeIdx, ((coverOf G).sProd s q ≠ 0 ∨ (coverOf G).sProd s' q ≠ 0) →
    SubI G (intBox q) Sr ∨ DisjI G (intBox q) Y)
  (hSY : Sr ⊆ Y)
  (hagree : ∀ q ∈ (coverOf G).cubeIdx, SubI G (intBox q) Sr →
    (coverOf G).sProd s q = (coverOf G).sProd s' q)
  (hrow : ∀ z y : G.Ω 1, (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr →
    xDirichletOperator G a aT x₀ ν α z y ≠ 0 →
    (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y)
include D D' hφ hδ hsm hdich hSY hagree hrow

/-- **Exact agreement of `Z = Ĝ - Π`.**  If every active cube of `s` or `s'` lies inside `Sr` or is
disjoint from `Y ⊇ Sr`, the parameters agree on the cubes inside `Sr`, the rows of the operator
from `Sr` stay in `Y`, and `w = w'` on `Sr`, then `Z_s w = Z_{s'} w'` on all of `Y`. -/
theorem decZ_exact {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr → ∀ i,
      w (y, i) = w' (y, i)) :
    ∀ y : G.Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i,
      (decZ G a aT x₀ ν α s φ *ᵥ w) (y, i) = (decZ G a aT x₀ ν α s' φ *ᵥ w') (y, i) := by
  classical
  have S := D.st
  have hx := D.x0
  have hα := D.pot
  have hU := D.isUnit_one_sub
  have hU' := D'.isUnit_one_sub
  have H0 : XWeight G 0 (fun _ => 0) := D.weight_zero
  have H0' : XWeight G 0 (fun _ => 0) := D'.weight_zero
  have hMs := decM_isUnit_cover D hφ hδ hsm
  have hMs' := decM_isUnit_cover D' hφ hδ hsm
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hMs
  have hdet' := (Matrix.isUnit_iff_isUnit_det _).1 hMs'
  obtain ⟨v, hv⟩ : ∃ v : G.Ω 1 → ℂ, v = (decM G a aT x₀ ν α s φ)⁻¹ *ᵥ
      (decN G a aT x₀ ν α s φ *ᵥ w) := ⟨_, rfl⟩
  obtain ⟨v', hv'⟩ : ∃ v : G.Ω 1 → ℂ, v = (decM G a aT x₀ ν α s' φ)⁻¹ *ᵥ
      (decN G a aT x₀ ν α s' φ *ᵥ w') := ⟨_, rfl⟩
  have hMv : decM G a aT x₀ ν α s φ *ᵥ v = decN G a aT x₀ ν α s φ *ᵥ w := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hMv' : decM G a aT x₀ ν α s' φ *ᵥ v' = decN G a aT x₀ ν α s' φ *ᵥ w' := by
    rw [hv', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet', Matrix.one_mulVec]
  obtain ⟨T, hT⟩ : ∃ T : (G.Ω 1 → ℂ) → (G.Ω 1 → ℂ), T = fun u =>
      decN G a aT x₀ ν α s φ *ᵥ w + u - decM G a aT x₀ ν α s φ *ᵥ u := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T : (G.Ω 1 → ℂ) → (G.Ω 1 → ℂ), T = fun u =>
      decN G a aT x₀ ν α s' φ *ᵥ w' + u - decM G a aT x₀ ν α s' φ *ᵥ u := ⟨_, rfl⟩
  have hTv : ∀ u, T u - v = (u - v) - decM G a aT x₀ ν α s φ *ᵥ (u - v) := by
    intro u
    subst hT
    show decN G a aT x₀ ν α s φ *ᵥ w + u - decM G a aT x₀ ν α s φ *ᵥ u - v = _
    rw [Matrix.mulVec_sub, hMv]
    abel
  have hTv' : ∀ u, T' u - v' = (u - v') - decM G a aT x₀ ν α s' φ *ᵥ (u - v') := by
    intro u
    subst hT'
    show decN G a aT x₀ ν α s' φ *ᵥ w' + u - decM G a aT x₀ ν α s' φ *ᵥ u - v' = _
    rw [Matrix.mulVec_sub, hMv']
    abel
  have hS0 := agmonSource_nonneg G 0 (fun _ => 0)
  have hc : ∀ u, agmonSource G 0 (fun _ => 0) (T u - v) ≤
      (1 / 4) * agmonSource G 0 (fun _ => 0) (u - v) := by
    intro u
    rw [hTv]
    refine (decM_error_le_cover D H0 hφ hδ (u - v)).trans ?_
    exact mul_le_mul_of_nonneg_right hsm (hS0 _)
  have hc' : ∀ u, agmonSource G 0 (fun _ => 0) (T' u - v') ≤
      (1 / 4) * agmonSource G 0 (fun _ => 0) (u - v') := by
    intro u
    rw [hTv']
    refine (decM_error_le_cover D' H0' hφ hδ (u - v')).trans ?_
    exact mul_le_mul_of_nonneg_right hsm (hS0 _)
  have hag : ∀ u u' : G.Ω 1 → ℂ,
      (∀ z ∈ {z : G.Ω 1 | (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr}, u z = u' z) →
      ∀ z ∈ {z : G.Ω 1 | (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr},
        T u z = T' u' z := by
    intro u u' huu z hz
    have hz' : (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr := hz
    subst hT hT'
    show (decN G a aT x₀ ν α s φ *ᵥ w + u - decM G a aT x₀ ν α s φ *ᵥ u) z =
      (decN G a aT x₀ ν α s' φ *ᵥ w' + u' - decM G a aT x₀ ν α s' φ *ᵥ u') z
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [decN_exact (φ := φ) S hx hα hU hU' hdich hSY hagree hrow hw hz', huu z hz,
      decM_exact (φ := φ) S hx hα hU hU' hdich hSY hagree hrow (fun y hy => huu y hy) hz']
  have hfix := fixed_point_agree T T' v v'
    {z : G.Ω 1 | (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ Sr} hc hc' hag
  intro y hy i
  have hZ : ∀ (ss : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℂ) (ww : G.Ω 1 × Fin N → ℂ)
      (Mi : G.Ω 1 → ℂ),
      Mi = (decM G a aT x₀ ν α ss φ)⁻¹ *ᵥ (decN G a aT x₀ ν α ss φ *ᵥ ww) →
      decZ G a aT x₀ ν α ss φ *ᵥ ww = liftOp N (Gsx G a aT x₀ ν α ss) *ᵥ ww -
        liftOp N (Gsx G a aT x₀ ν α ss) *ᵥ (fieldMul (restrictField G φ) *ᵥ Mi) := by
    intro ss ww Mi hMi
    unfold decZ decPi
    rw [Matrix.sub_mulVec, hMi]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have e1 := Gvec_exact S hx hα hU hU' hdich hSY hagree hw y hy i
  have e2 := Gvec_exact S hx hα hU hU' hdich hSY hagree
    (w := fieldMul (restrictField G φ) *ᵥ v) (w' := fieldMul (restrictField G φ) *ᵥ v')
    (fun y hy i => by
      rw [fieldMul_mulVec, fieldMul_mulVec, hfix y hy]) y hy i
  rw [hZ s w v hv, hZ s' w' v' hv', Pi.sub_apply, Pi.sub_apply, e1, e2]

end ZExact2

section RowGeometry

/-- A non-zero entry of the shifted Dirichlet operator joins a site to itself, to a lattice
neighbour, or to a site of its layer block. -/
theorem xDirichlet_row_cases (α : G.Ω 1 → ℂ) {p q : G.Ω 1}
    (h : xDirichletOperator G a aT x₀ ν α p q ≠ 0) :
    (q : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) = p ∨
      (∃ μ : Fin d, (q : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) =
          (p : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1 ∨
        (q : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) =
          (p : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) ∨
      (q : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈
        G.blk (G.layerIndex (p : Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  exact h (xDirichlet_entry_eq_zero (G := G) (a := a) (aT := aT) (x₀ := x₀) (ν := ν) α h1
    (fun μ => ⟨fun e => (h2 μ).1 e, fun e => (h2 μ).2 e⟩) h3)

end RowGeometry

end Exact

section CovExact

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx x : ℝ}

/-- **Exact core agreement of the shifted covariance, uniformly in `x`.**  Let `Sr ⊆ Y` be sets of
cubes such that every active cube of `s` or `s'` (non-zero product of its parameters) lies inside
`Sr` or is disjoint from `Y`, the parameters agree on the cubes inside `Sr`, and `Y` contains the
lattice and layer-block neighbours of the sites of `Sr`.  Then the rows of the shifted covariance
`(1 + x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` at the sites of `Y` do not depend on `s`. -/
theorem baseCovX_exact {κ δ : ℝ} {α : G.Ω 1 → ℂ}
    {s s' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    (S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx) (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hα : AdmPot G α)
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {Sr Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)} (hSY : Sr ⊆ Y)
    (hdich : ∀ q ∈ (coverOf G).cubeIdx,
      ((coverOf G).sProd s q ≠ 0 ∨ (coverOf G).sProd s' q ≠ 0) →
      SubI G (intBox q) Sr ∨ DisjI G (intBox q) Y)
    (hagree : ∀ q ∈ (coverOf G).cubeIdx, SubI G (intBox q) Sr →
      (coverOf G).sProd s q = (coverOf G).sProd s' q)
    (hnbr : ∀ p q : G.Ω 1, (p : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Sr →
      ((q : Balaban.Localization.CTorus d L N₁ m₁ 1) = p ∨
        (∃ μ : Fin d, (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
            (p : Balaban.Localization.CTorus d L N₁ m₁ 1) + Pi.single μ 1 ∨
          (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
            (p : Balaban.Localization.CTorus d L N₁ m₁ 1) - Pi.single μ 1) ∨
        (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈
          G.blk (G.layerIndex (p : Balaban.Localization.CTorus d L N₁ m₁ 1)) p) →
      (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (hφ : IsConstraintField G δ φ)
    (y z : G.Ω 1 × Fin N) (hy : (y.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y) :
    ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z =
      ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s') -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s' φ) y z := by
  rw [baseCovX_eq_add_decZ, baseCovX_eq_add_decZ]
  have D : Dec2.XData (coverOf G) G a aT (ν + x) 0 α κ s Cx := ⟨S, hCx, hα, le_rfl, hκ, hM, hs⟩
  have D' : Dec2.XData (coverOf G) G a aT (ν + x) 0 α κ s' Cx := ⟨S, hCx, hα, le_rfl, hκ, hM, hs'⟩
  have h := decZ_exact D D' hφ hδ hsm hdich hSY hagree
    (fun p q hp hpq => hnbr p q hp (xDirichlet_row_cases α hpq))
    (w := (Pi.single z 1 : G.Ω 1 × Fin N → ℂ)) (w' := (Pi.single z 1 : G.Ω 1 × Fin N → ℂ))
    (fun _ _ _ => rfl) y.1 hy y.2
  rw [mulVec_single_entry, mulVec_single_entry] at h
  simp only [Matrix.add_apply]
  rw [h]

end CovExact

section Interp

open MeasureTheory Set

/-- An integrand `x^{-1/2} F(x)` with `0 ≤ F ≤ min (A / (1 + x)) b` has integral at most
`4 √(A b)` on `(0, ∞)`. -/
theorem stieltjes_interp {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) {F : ℝ → ℝ}
    (hF0 : ∀ x, 0 < x → 0 ≤ F x) (hF1 : ∀ x, 0 < x → F x ≤ A / (1 + x))
    (hF2 : ∀ x, 0 < x → F x ≤ b)
    (hint : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * F x) (Ioi 0)) :
    ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * F x ≤ 4 * Real.sqrt (A * b) := by
  have hr0 : ∀ x : ℝ, 0 < x → 0 < x ^ (-(1 / 2 : ℝ)) := fun x hx => Real.rpow_pos_of_pos hx _
  rcases hA.eq_or_lt with hA0 | hApos
  · have hz : ∀ x ∈ Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * F x = 0 := by
      intro x hx
      have hx' : 0 < x := hx
      have : F x ≤ 0 := by have := hF1 x hx'; rwa [← hA0, zero_div] at this
      rw [le_antisymm this (hF0 x hx'), mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hz, integral_zero, ← hA0, zero_mul,
      Real.sqrt_zero, mul_zero]
  rcases hb.eq_or_lt with hb0 | hbpos
  · have hz : ∀ x ∈ Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * F x = 0 := by
      intro x hx
      have hx' : 0 < x := hx
      have : F x ≤ 0 := by have := hF2 x hx'; rwa [← hb0] at this
      rw [le_antisymm this (hF0 x hx'), mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hz, integral_zero, ← hb0, mul_zero,
      Real.sqrt_zero, mul_zero]
  set X : ℝ := A / b with hXdef
  have hX : 0 < X := div_pos hApos hbpos
  have hsplit : ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * F x =
      (∫ x in Ioc (0 : ℝ) X, x ^ (-(1 / 2 : ℝ)) * F x) +
        ∫ x in Ioi X, x ^ (-(1 / 2 : ℝ)) * F x := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hX.le]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set (Set.Ioc_subset_Ioi_self)) (hint.mono_set (Set.Ioi_subset_Ioi hX.le))
  -- the part near zero
  have hI1 : IntegrableOn (fun x : ℝ => b * x ^ (-(1 / 2 : ℝ))) (Ioc 0 X) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := X)
      (r := -(1 / 2 : ℝ)) (by norm_num)).1
    exact this.const_mul b
  have hP1 : ∫ x in Ioc (0 : ℝ) X, x ^ (-(1 / 2 : ℝ)) * F x ≤
      ∫ x in Ioc (0 : ℝ) X, b * x ^ (-(1 / 2 : ℝ)) := by
    refine setIntegral_mono_on (hint.mono_set Set.Ioc_subset_Ioi_self) hI1 measurableSet_Ioc
      fun x hx => ?_
    have hx' : 0 < x := hx.1
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hF2 x hx') (hr0 x hx').le
  have hV1 : ∫ x in Ioc (0 : ℝ) X, b * x ^ (-(1 / 2 : ℝ)) = 2 * b * X ^ (1 / 2 : ℝ) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hX.le,
      integral_rpow (Or.inl (by norm_num))]
    rw [Real.zero_rpow (by norm_num)]
    norm_num
    ring
  -- the tail
  have hI2 : IntegrableOn (fun x : ℝ => A * x ^ (-(3 / 2 : ℝ))) (Ioi X) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hX).const_mul A
  have hP2 : ∫ x in Ioi X, x ^ (-(1 / 2 : ℝ)) * F x ≤ ∫ x in Ioi X, A * x ^ (-(3 / 2 : ℝ)) := by
    refine setIntegral_mono_on (hint.mono_set (Set.Ioi_subset_Ioi hX.le)) hI2 measurableSet_Ioi
      fun x hx => ?_
    have hx' : 0 < x := lt_trans hX hx
    have h1 : F x ≤ A * x⁻¹ := by
      refine (hF1 x hx').trans ?_
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hx' (by linarith)) hA
    have h2 : x ^ (-(3 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ)) * x⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hx']; norm_num
    rw [h2]
    calc x ^ (-(1 / 2 : ℝ)) * F x ≤ x ^ (-(1 / 2 : ℝ)) * (A * x⁻¹) :=
          mul_le_mul_of_nonneg_left h1 (hr0 x hx').le
      _ = _ := by ring
  have hV2 : ∫ x in Ioi X, A * x ^ (-(3 / 2 : ℝ)) = 2 * A * X ^ (-(1 / 2 : ℝ)) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hX]
    norm_num
    ring
  rw [hsplit]
  refine (add_le_add hP1 hP2).trans ?_
  rw [hV1, hV2]
  have hsA := Real.sqrt_pos.2 hApos
  have hsb := Real.sqrt_pos.2 hbpos
  have e1 : X ^ (1 / 2 : ℝ) = Real.sqrt A / Real.sqrt b := by
    rw [← Real.sqrt_eq_rpow, hXdef, Real.sqrt_div hA]
  have e2 : X ^ (-(1 / 2 : ℝ)) = Real.sqrt b / Real.sqrt A := by
    rw [Real.rpow_neg hX.le, ← Real.sqrt_eq_rpow, hXdef, Real.sqrt_div hA, inv_div]
  rw [e1, e2, Real.sqrt_mul hA]
  have hbb : b = Real.sqrt b * Real.sqrt b := (Real.mul_self_sqrt hb).symm
  have hAA : A = Real.sqrt A * Real.sqrt A := (Real.mul_self_sqrt hA).symm
  apply le_of_eq
  field_simp
  nlinarith [hbb, hAA]

end Interp

section SqrtIntegrable

open MeasureTheory Set

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx : ℝ}

/-- The integrand of the Stieltjes square root is integrable on `(0, ∞)`, for every parameter
family on the discs `‖s_P‖ ≤ e^κ`. -/
theorem baseCovX_integrand_integrableOn {κ δ : ℝ} {α : G.Ω 1 → ℂ}
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hα : AdmPot G α)
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (hφ : IsConstraintField G δ φ)
    (y z : G.Ω 1 × Fin N) :
    IntegrableOn (fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
        liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
        Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z) (Ioi 0) := by
  obtain ⟨B, hB0, hdec⟩ := baseCovX_decay d L κ
  have hν : 0 ≤ ν := S.mass
  have hD : ∀ x : ℝ, 0 ≤ x → Dec2.XData (coverOf G) G a aT (ν + x) 0 α κ s Cx :=
    fun x hx => ⟨xCover_add_mass S hx, hCx, hα, le_rfl, hκ, hM, hs⟩
  have hrpow : ContinuousOn (fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (Ioi 0) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact fun y hy =>
      (Real.continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp hy).ne')).continuousWithinAt
  have hbd : ∀ x : ℝ, 0 < x →
      ‖((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z‖ ≤
        B * (x ^ (-(1 / 2 : ℝ)) * (1 + x)⁻¹) := by
    intro x hx
    have h3 : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx _
    have hpt := hdec (xCover_add_mass S hx.le) hCx hν hx.le hκ hM hδ hsm hα hs hφ y z
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h3.le]
    calc x ^ (-(1 / 2 : ℝ)) * _ ≤ x ^ (-(1 / 2 : ℝ)) * (B / (1 + x)) :=
          mul_le_mul_of_nonneg_left hpt h3.le
      _ = _ := by rw [div_eq_mul_inv]; ring
  have hcont : ContinuousOn (fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z) (Ioi 0) := by
    have h := continuousOn_baseCovX_shift (fun x hx => hD x hx) hφ hδ hsm
    exact hrpow.mul ((continuousOn_pi.1 (continuousOn_pi.1 h y) z).mono Ioi_subset_Ici_self)
  have hgi : IntegrableOn (fun x : ℝ => B * (x ^ (-(1 / 2 : ℝ)) * (1 + x)⁻¹)) (Ioi 0) :=
    (Localization.integrableOn_rpow_inv_add one_pos).const_mul B
  refine Integrable.mono' hgi ((hcont).aestronglyMeasurable measurableSet_Ioi) ?_
  exact (ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun x hx => hbd x (mem_Ioi.mp hx))

/-- **Exact core agreement of the Stieltjes square root.**  Under the hypotheses of
`baseCovX_exact` (which do not involve the shift), the rows of `π⁻¹ ∫₀^∞ x^{-1/2} C_x(s) dx` at the
sites of `Y` do not depend on `s`. -/
theorem baseCovX_sqrt_exact {κ δ : ℝ} {α : G.Ω 1 → ℂ}
    {s s' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hα : AdmPot G α)
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {Sr Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)} (hSY : Sr ⊆ Y)
    (hdich : ∀ q ∈ (coverOf G).cubeIdx,
      ((coverOf G).sProd s q ≠ 0 ∨ (coverOf G).sProd s' q ≠ 0) →
      SubI G (intBox q) Sr ∨ DisjI G (intBox q) Y)
    (hagree : ∀ q ∈ (coverOf G).cubeIdx, SubI G (intBox q) Sr →
      (coverOf G).sProd s q = (coverOf G).sProd s' q)
    (hnbr : ∀ p q : G.Ω 1, (p : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Sr →
      ((q : Balaban.Localization.CTorus d L N₁ m₁ 1) = p ∨
        (∃ μ : Fin d, (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
            (p : Balaban.Localization.CTorus d L N₁ m₁ 1) + Pi.single μ 1 ∨
          (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
            (p : Balaban.Localization.CTorus d L N₁ m₁ 1) - Pi.single μ 1) ∨
        (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈
          G.blk (G.layerIndex (p : Balaban.Localization.CTorus d L N₁ m₁ 1)) p) →
      (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (hφ : IsConstraintField G δ φ)
    (y z : G.Ω 1 × Fin N) (hy : (y.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y) :
    ((1 / Real.pi : ℝ) : ℂ) * ∫ x in Ioi (0 : ℝ), ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z =
      ((1 / Real.pi : ℝ) : ℂ) * ∫ x in Ioi (0 : ℝ), ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s') -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s' φ) y z := by
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [baseCovX_exact (xCover_add_mass S (mem_Ioi.mp hx).le) hCx hκ hM hδ hsm hα hs hs' hSY hdich
    hagree hnbr hφ y z hy]

end SqrtIntegrable

section SqrtCompare

open MeasureTheory Set

/-- **Weighted comparison of the Stieltjes square root.**  For two parameter families on the
discs `‖s_P‖ ≤ e^κ` that are `1` on every cube whose interaction cube is not inside `W`, the
entries of `π⁻¹ ∫₀^∞ x^{-1/2} C_x(s) dx` differ by `B e^{-γ r(y) / 2}`, `r` the path distance from
`y` to `W` truncated at any `T`, `γ = xAgmonRate d L`; `B` depends only on `d, L, κ`.  (The
weighted bound of the covariance is uniform in the shift and the decay `B/(1 + x)` of
`baseCovX_decay` makes the integral converge; their interpolation costs half the rate.) -/
theorem baseCovX_sqrt_sub_decay (d L : ℕ) [NeZero L] (κ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N₁ m₁ N : ℕ} [NeZero N₁] {ϱ : ℝ}
      {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx : ℝ}
      {δ : ℝ} {α : G.Ω 1 → ℂ} {s s' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
      (_S : Dec2.XCover (coverOf G) G a aT ν Cx) (_hCx : 0 ≤ Cx) (_hκ : 0 ≤ κ)
      (_hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (_hδ : 0 ≤ δ)
      (_hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (_hα : AdmPot G α)
      (_hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (_hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
      {W : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)}
      (_hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W)
      (_hW' : ∀ z ∈ cubeIdx G, sProd G s' z ≠ 1 → intBox z ⊆ W)
      {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
      (_hφ : IsConstraintField G δ φ) (T : ℝ) (y z : G.Ω 1 × Fin N),
      ‖((1 / Real.pi : ℝ) : ℂ) * (∫ x in Ioi (0 : ℝ), ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
            liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
            Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z) -
        ((1 / Real.pi : ℝ) : ℂ) * (∫ x in Ioi (0 : ℝ), ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
            liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s') -
            Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s' φ) y z)‖ ≤
        B * Real.exp (-(xAgmonRate d L * truncSetDistR G W T y.1 / 2)) := by
  obtain ⟨B1, hB1, hdec⟩ := baseCovX_decay d L κ
  set Kc : ℝ := Real.sqrt (zCloseConst d L * Real.exp (N0 d L * κ) ^ 2) * ((L : ℝ) ^ 2) with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  refine ⟨4 / Real.pi * Real.sqrt (2 * B1 * (2 * Kc)), by positivity, ?_⟩
  intro N₁ m₁ N _ ϱ G a aT ν Cx δ α s s' S hCx hκ hM hδ hsm hα hs hs' W hW hW' φ hφ T y z
  have hν : 0 ≤ ν := S.mass
  set E : ℝ := Real.exp (-(xAgmonRate d L * truncSetDistR G W T y.1)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have i1 := baseCovX_integrand_integrableOn S hCx hκ hM hδ hsm hα hs hφ y z
  have i2 := baseCovX_integrand_integrableOn S hCx hκ hM hδ hsm hα hs' hφ y z
  have hF0 : ∀ x : ℝ, 0 < x → 0 ≤ ‖((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z -
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s') -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s' φ) y z‖ := fun _ _ => norm_nonneg _
  have hF1 : ∀ x : ℝ, 0 < x → ‖((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z -
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s') -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s' φ) y z‖ ≤ (2 * B1) / (1 + x) := by
    intro x hx
    have h1 := hdec (xCover_add_mass S hx.le) hCx hν hx.le hκ hM hδ hsm hα hs hφ y z
    have h2 := hdec (xCover_add_mass S hx.le) hCx hν hx.le hκ hM hδ hsm hα hs' hφ y z
    refine (norm_sub_le _ _).trans ?_
    have : 2 * B1 / (1 + x) = B1 / (1 + x) + B1 / (1 + x) := by ring
    rw [this]
    exact add_le_add h1 h2
  have hF2 : ∀ x : ℝ, 0 < x → ‖((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z -
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s') -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s' φ) y z‖ ≤ 2 * Kc * E := by
    intro x hx
    exact baseCovX_sub_decay (xCover_add_mass S hx.le) hCx hκ hM hδ hsm hα hs hs' hW hW' hφ T y z
  have hpt : ∀ x ∈ Ioi (0 : ℝ),
      ‖((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z -
      ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s') -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s' φ) y z‖ =
      x ^ (-(1 / 2 : ℝ)) * ‖((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z -
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s') -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s' φ) y z‖ := by
    intro x hx
    have h3 : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (mem_Ioi.mp hx) _
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg h3.le]
  have hint' : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) *
      ‖((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z -
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s') -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s' φ) y z‖) (Ioi 0) :=
    Integrable.congr (i1.sub i2).norm
      ((ae_restrict_iff' measurableSet_Ioi).2
        (Filter.Eventually.of_forall fun x hx => hpt x hx))
  have hI := stieltjes_interp (A := 2 * B1) (b := 2 * Kc * E) (by positivity) (by positivity)
    hF0 hF1 hF2 hint'
  -- the norm of the difference of the integrals
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    ← integral_sub i1 i2]
  have hn := norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z -
      ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s') -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s' φ) y z)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hpt x hx)] at hn
  have hsq : Real.sqrt (2 * B1 * (2 * Kc * E)) =
      Real.sqrt (2 * B1 * (2 * Kc)) * Real.exp (-(xAgmonRate d L * truncSetDistR G W T y.1 / 2)) := by
    have e1 : 2 * B1 * (2 * Kc * E) = (2 * B1 * (2 * Kc)) * E := by ring
    rw [e1, Real.sqrt_mul (by positivity)]
    congr 1
    have e2 : E = Real.exp (-(xAgmonRate d L * truncSetDistR G W T y.1 / 2)) *
        Real.exp (-(xAgmonRate d L * truncSetDistR G W T y.1 / 2)) := by
      rw [hE, ← Real.exp_add]; congr 1; ring
    rw [e2, Real.sqrt_mul_self (Real.exp_pos _).le]
  have hpi := Real.pi_pos
  calc 1 / Real.pi * ‖∫ x in Ioi (0 : ℝ), _‖ ≤ 1 / Real.pi * (4 * Real.sqrt (2 * B1 * (2 * Kc * E))) :=
        mul_le_mul_of_nonneg_left (hn.trans hI) (by positivity)
    _ = _ := by rw [hsq]; ring

end SqrtCompare

end Balaban.LargeField.Base
