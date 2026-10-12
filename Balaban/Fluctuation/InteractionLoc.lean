/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionDir
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Localized expansions of the interaction, and their calculus (FLUCTUATION §3.3, Prop. 3.3)

`LocInt` is the conclusion of Proposition 3.3 for one function: a value `val(x₀, w, σ, Θ)` (the
interaction built from the fluctuation direction `x₀` of the ray and the direction `w`, the
parameter `σ`, and the data `Θ`) is a finite sum `∑_Y T_Y` of terms that are analytic in
`(Θ, σ)`, bounded by `|σ| b_Y`, local (they depend on `Θ` through `AgΘ` and on `(x₀, w)` through
`AgF`), and vanish at `σ = 0`.  The terms of the old effective action, of the source, and of the
interaction potential are added with `LocInt.add`, `LocInt.sum`, scaled with `LocInt.smul`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Set Metric

section LocInt

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*}
variable {ι : Type*}

/-- **A localized expansion** `val = ∑_{Y ∈ 𝒴} T_Y` with the properties of Proposition 3.3. -/
structure LocInt (S : Set Λ) (XW : Set (F × F)) (Rσ : ℝ) (𝒴 : Finset ι)
    (T : ι → F → F → ℂ → Λ → ℂ) (val : F → F → ℂ → Λ → ℂ) (b : ι → ℝ)
    (AgΘ : ι → Λ → Λ → Prop) (AgF : ι → F → F → Prop) : Prop where
  sum : ∀ xw ∈ XW, ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ Θ ∈ S,
    val xw.1 xw.2 σ Θ = ∑ Y ∈ 𝒴, T Y xw.1 xw.2 σ Θ
  analytic : ∀ Y ∈ 𝒴, ∀ xw ∈ XW,
    AnalyticOnNhd ℂ (fun p : Λ × ℂ => T Y xw.1 xw.2 p.2 p.1) (S ×ˢ ball (0 : ℂ) Rσ)
  bound : ∀ Y ∈ 𝒴, ∀ xw ∈ XW, ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ Θ ∈ S, ‖T Y xw.1 xw.2 σ Θ‖ ≤ ‖σ‖ * b Y
  loc : ∀ Y ∈ 𝒴, ∀ xw ∈ XW, ∀ xw' ∈ XW, ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ Θ ∈ S, ∀ Θ' ∈ S,
    AgΘ Y Θ Θ' → AgF Y xw.1 xw'.1 → AgF Y xw.2 xw'.2 →
    T Y xw.1 xw.2 σ Θ = T Y xw'.1 xw'.2 σ Θ'
  zero : ∀ Y ∈ 𝒴, ∀ xw ∈ XW, ∀ Θ ∈ S, T Y xw.1 xw.2 0 Θ = 0

variable {S : Set Λ} {XW : Set (F × F)} {Rσ : ℝ} {AgΘ : ι → Λ → Λ → Prop}
  {AgF : ι → F → F → Prop}

/-- Weakening the bound. -/
theorem LocInt.mono {𝒴 : Finset ι} {T : ι → F → F → ℂ → Λ → ℂ} {val : F → F → ℂ → Λ → ℂ}
    {b b' : ι → ℝ} (h : LocInt S XW Rσ 𝒴 T val b AgΘ AgF) (hb : ∀ Y, b Y ≤ b' Y) :
    LocInt S XW Rσ 𝒴 T val b' AgΘ AgF :=
  { h with bound := fun Y hY xw hxw σ hσ Θ hΘ =>
      (h.bound Y hY xw hxw σ hσ Θ hΘ).trans (mul_le_mul_of_nonneg_left (hb Y) (norm_nonneg _)) }

/-- Multiplication by a constant. -/
theorem LocInt.smul {𝒴 : Finset ι} {T : ι → F → F → ℂ → Λ → ℂ} {val : F → F → ℂ → Λ → ℂ}
    {b : ι → ℝ} (h : LocInt S XW Rσ 𝒴 T val b AgΘ AgF) (c : ℂ) :
    LocInt S XW Rσ 𝒴 (fun Y x w σ Θ => c * T Y x w σ Θ) (fun x w σ Θ => c * val x w σ Θ)
      (fun Y => ‖c‖ * b Y) AgΘ AgF where
  sum := fun xw hxw σ hσ Θ hΘ => by
    rw [h.sum xw hxw σ hσ Θ hΘ, Finset.mul_sum]
  analytic := fun Y hY xw hxw => (analyticOnNhd_const).mul (h.analytic Y hY xw hxw)
  bound := fun Y hY xw hxw σ hσ Θ hΘ => by
    rw [norm_mul]
    calc ‖c‖ * ‖T Y xw.1 xw.2 σ Θ‖ ≤ ‖c‖ * (‖σ‖ * b Y) :=
          mul_le_mul_of_nonneg_left (h.bound Y hY xw hxw σ hσ Θ hΘ) (norm_nonneg _)
      _ = ‖σ‖ * (‖c‖ * b Y) := by ring
  loc := fun Y hY xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' h1 h2 h3 => by
    rw [h.loc Y hY xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' h1 h2 h3]
  zero := fun Y hY xw hxw Θ hΘ => by rw [h.zero Y hY xw hxw Θ hΘ, mul_zero]

/-- Finite sums of localized expansions over a family of terms `τ ∈ 𝒯`, with label sets `𝒴 τ`. -/
theorem LocInt.finsum {κ : Type*} [DecidableEq ι] (𝒯 : Finset κ) {𝒴 : κ → Finset ι}
    {T : κ → ι → F → F → ℂ → Λ → ℂ} {val : κ → F → F → ℂ → Λ → ℂ} {b : κ → ι → ℝ}
    (h : ∀ τ ∈ 𝒯, LocInt S XW Rσ (𝒴 τ) (T τ) (val τ) (b τ) AgΘ AgF) :
    LocInt S XW Rσ (𝒯.biUnion 𝒴)
      (fun Y x w σ Θ => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then T τ Y x w σ Θ else 0)
      (fun x w σ Θ => ∑ τ ∈ 𝒯, val τ x w σ Θ)
      (fun Y => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then b τ Y else 0) AgΘ AgF where
  sum := fun xw hxw σ hσ Θ hΘ => by
    classical
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [(h τ hτ).sum xw hxw σ hσ Θ hΘ, Finset.sum_ite_mem,
      Finset.inter_eq_right.2 (Finset.subset_biUnion_of_mem 𝒴 hτ)]
  analytic := fun Y _ xw hxw => by
    classical
    intro p hp
    refine Finset.analyticAt_fun_sum _ fun τ hτ => ?_
    by_cases hY : Y ∈ 𝒴 τ
    · simpa [hY] using (h τ hτ).analytic Y hY xw hxw p hp
    · simp only [hY, ite_false]; exact analyticAt_const
  bound := fun Y _ xw hxw σ hσ Θ hΘ => by
    classical
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun τ hτ => ?_
    by_cases hY : Y ∈ 𝒴 τ
    · simpa [hY] using (h τ hτ).bound Y hY xw hxw σ hσ Θ hΘ
    · simp [hY]
  loc := fun Y _ xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' h1 h2 h3 => by
    classical
    refine Finset.sum_congr rfl fun τ hτ => ?_
    by_cases hY : Y ∈ 𝒴 τ
    · simp only [hY, ite_true]
      exact (h τ hτ).loc Y hY xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' h1 h2 h3
    · simp [hY]
  zero := fun Y _ xw hxw Θ hΘ => by
    classical
    refine Finset.sum_eq_zero fun τ hτ => ?_
    by_cases hY : Y ∈ 𝒴 τ
    · simp only [hY, ite_true]; exact (h τ hτ).zero Y hY xw hxw Θ hΘ
    · simp [hY]

/-- Restriction of the set of admissible directions. -/
theorem LocInt.mono_XW {𝒴 : Finset ι} {T : ι → F → F → ℂ → Λ → ℂ} {val : F → F → ℂ → Λ → ℂ}
    {b : ι → ℝ} (h : LocInt S XW Rσ 𝒴 T val b AgΘ AgF) {XW' : Set (F × F)} (hsub : XW' ⊆ XW) :
    LocInt S XW' Rσ 𝒴 T val b AgΘ AgF where
  sum := fun xw hxw => h.sum xw (hsub hxw)
  analytic := fun Y hY xw hxw => h.analytic Y hY xw (hsub hxw)
  bound := fun Y hY xw hxw => h.bound Y hY xw (hsub hxw)
  loc := fun Y hY xw hxw xw' hxw' => h.loc Y hY xw (hsub hxw) xw' (hsub hxw')
  zero := fun Y hY xw hxw => h.zero Y hY xw (hsub hxw)

/-- Strengthening the agreement relations. -/
theorem LocInt.mono_Ag {𝒴 : Finset ι} {T : ι → F → F → ℂ → Λ → ℂ} {val : F → F → ℂ → Λ → ℂ}
    {b : ι → ℝ} (h : LocInt S XW Rσ 𝒴 T val b AgΘ AgF) {AgΘ' : ι → Λ → Λ → Prop}
    {AgF' : ι → F → F → Prop} (h1 : ∀ Y Θ Θ', AgΘ' Y Θ Θ' → AgΘ Y Θ Θ')
    (h2 : ∀ Y a a', AgF' Y a a' → AgF Y a a') :
    LocInt S XW Rσ 𝒴 T val b AgΘ' AgF' where
  sum := h.sum
  analytic := h.analytic
  bound := h.bound
  loc := fun Y hY xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' a b' c =>
    h.loc Y hY xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' (h1 _ _ _ a) (h2 _ _ _ b') (h2 _ _ _ c)
  zero := h.zero

/-- The sum of two localized expansions with the same labels and bounds added. -/
theorem LocInt.add₂ [DecidableEq ι] {𝒴 𝒴' : Finset ι} {T T' : ι → F → F → ℂ → Λ → ℂ}
    {val val' : F → F → ℂ → Λ → ℂ} {b b' : ι → ℝ} (h : LocInt S XW Rσ 𝒴 T val b AgΘ AgF)
    (h' : LocInt S XW Rσ 𝒴' T' val' b' AgΘ AgF) :
    LocInt S XW Rσ (𝒴 ∪ 𝒴')
      (fun Y x w σ Θ => (if Y ∈ 𝒴 then T Y x w σ Θ else 0) +
        (if Y ∈ 𝒴' then T' Y x w σ Θ else 0))
      (fun x w σ Θ => val x w σ Θ + val' x w σ Θ)
      (fun Y => (if Y ∈ 𝒴 then b Y else 0) + (if Y ∈ 𝒴' then b' Y else 0)) AgΘ AgF where
  sum := fun xw hxw σ hσ Θ hΘ => by
    classical
    rw [h.sum xw hxw σ hσ Θ hΘ, h'.sum xw hxw σ hσ Θ hΘ, Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_subset (Finset.subset_union_left (s₂ := 𝒴')) (fun Y _ hY => by simp [hY])]
      exact Finset.sum_congr rfl fun Y hY => by simp [hY]
    · rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := 𝒴)) (fun Y _ hY => by simp [hY])]
      exact Finset.sum_congr rfl fun Y hY => by simp [hY]
  analytic := fun Y _ xw hxw => by
    classical
    by_cases h1 : Y ∈ 𝒴 <;> by_cases h2 : Y ∈ 𝒴'
    · simp only [h1, h2, ite_true]
      intro p hp
      exact (h.analytic Y h1 xw hxw p hp).add (h'.analytic Y h2 xw hxw p hp)
    · simpa [h1, h2] using h.analytic Y h1 xw hxw
    · simpa [h1, h2] using h'.analytic Y h2 xw hxw
    · exfalso; rename_i hu; simp [h1, h2] at hu
  bound := fun Y _ xw hxw σ hσ Θ hΘ => by
    classical
    by_cases h1 : Y ∈ 𝒴 <;> by_cases h2 : Y ∈ 𝒴'
    · simp only [h1, h2, ite_true]
      refine (norm_add_le _ _).trans ?_
      have := add_le_add (h.bound Y h1 xw hxw σ hσ Θ hΘ) (h'.bound Y h2 xw hxw σ hσ Θ hΘ)
      linarith
    · simpa [h1, h2] using h.bound Y h1 xw hxw σ hσ Θ hΘ
    · simpa [h1, h2] using h'.bound Y h2 xw hxw σ hσ Θ hΘ
    · exfalso; rename_i hu; simp [h1, h2] at hu
  loc := fun Y _ xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' a c d => by
    classical
    by_cases h1 : Y ∈ 𝒴 <;> by_cases h2 : Y ∈ 𝒴'
    · simp only [h1, h2, ite_true]
      rw [h.loc Y h1 xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' a c d,
        h'.loc Y h2 xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' a c d]
    · simp only [h1, h2, ite_true, ite_false]
      rw [h.loc Y h1 xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' a c d]
    · simp only [h1, h2, ite_true, ite_false]
      rw [h'.loc Y h2 xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' a c d]
    · exfalso; rename_i hu; simp [h1, h2] at hu
  zero := fun Y _ xw hxw Θ hΘ => by
    classical
    by_cases h1 : Y ∈ 𝒴 <;> by_cases h2 : Y ∈ 𝒴'
    · simp [h1, h2, h.zero Y h1 xw hxw Θ hΘ, h'.zero Y h2 xw hxw Θ hΘ]
    · simp [h1, h2, h.zero Y h1 xw hxw Θ hΘ]
    · simp [h1, h2, h'.zero Y h2 xw hxw Θ hΘ]
    · exfalso; rename_i hu; simp [h1, h2] at hu

section Comap

variable {F' : Type*}

/-- **Pulling back along projections of the directions.** -/
theorem LocInt.comap {𝒴 : Finset ι} {T : ι → F → F → ℂ → Λ → ℂ} {val : F → F → ℂ → Λ → ℂ}
    {b : ι → ℝ} (h : LocInt S XW Rσ 𝒴 T val b AgΘ AgF) (π : F' → F) {XW' : Set (F' × F')}
    (hXW : ∀ xw ∈ XW', (π xw.1, π xw.2) ∈ XW) {AgF' : ι → F' → F' → Prop}
    (hAg : ∀ Y a a', AgF' Y a a' → AgF Y (π a) (π a')) :
    LocInt S XW' Rσ 𝒴 (fun Y x w σ Θ => T Y (π x) (π w) σ Θ)
      (fun x w σ Θ => val (π x) (π w) σ Θ) b AgΘ AgF' where
  sum := fun xw hxw => h.sum (π xw.1, π xw.2) (hXW xw hxw)
  analytic := fun Y hY xw hxw => h.analytic Y hY (π xw.1, π xw.2) (hXW xw hxw)
  bound := fun Y hY xw hxw => h.bound Y hY (π xw.1, π xw.2) (hXW xw hxw)
  loc := fun Y hY xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' a c d =>
    h.loc Y hY (π xw.1, π xw.2) (hXW xw hxw) (π xw'.1, π xw'.2) (hXW xw' hxw') σ hσ Θ hΘ Θ' hΘ'
      a (hAg _ _ _ c) (hAg _ _ _ d)
  zero := fun Y hY xw hxw => h.zero Y hY (π xw.1, π xw.2) (hXW xw hxw)

end Comap

section Amp

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- **Multiplication by an analytic amplitude depending on an extra parameter** (the source `g`):
`T_Y(Θ, g) = c(g) T_Y(Θ)`. -/
theorem LocInt.mulAmp {𝒴 : Finset ι} {T : ι → F → F → ℂ → Λ → ℂ} {val : F → F → ℂ → Λ → ℂ}
    {b : ι → ℝ} (h : LocInt S XW Rσ 𝒴 T val b AgΘ AgF) {SG : Set G} {amp : G → ℂ} {Ma : ℝ}
    (hamp : AnalyticOnNhd ℂ amp SG) (hMa : ∀ g ∈ SG, ‖amp g‖ ≤ Ma) {AgG : ι → G → G → Prop}
    (hloc : ∀ Y ∈ 𝒴, ∀ g ∈ SG, ∀ g' ∈ SG, AgG Y g g' → amp g = amp g') :
    LocInt (S ×ˢ SG) XW Rσ 𝒴 (fun Y x w σ p => amp p.2 * T Y x w σ p.1)
      (fun x w σ p => amp p.2 * val x w σ p.1) (fun Y => Ma * b Y)
      (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF where
  sum := fun xw hxw σ hσ p hp => by
    rw [h.sum xw hxw σ hσ p.1 hp.1, Finset.mul_sum]
  analytic := fun Y hY xw hxw => by
    rintro ⟨⟨Θ, g⟩, σ⟩ ⟨⟨hΘ, hg⟩, hσ⟩
    have h1 : AnalyticAt ℂ (fun q : (Λ × G) × ℂ => amp q.1.2) ((Θ, g), σ) :=
      (hamp g hg).comp_of_eq (analyticAt_snd.comp analyticAt_fst) rfl
    have h2 : AnalyticAt ℂ (fun q : (Λ × G) × ℂ => T Y xw.1 xw.2 q.2 q.1.1) ((Θ, g), σ) :=
      ((h.analytic Y hY xw hxw) (Θ, σ) ⟨hΘ, hσ⟩).comp_of_eq
        ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd) rfl
    exact h1.mul h2
  bound := fun Y hY xw hxw σ hσ p hp => by
    rw [norm_mul]
    calc ‖amp p.2‖ * ‖T Y xw.1 xw.2 σ p.1‖ ≤ Ma * (‖σ‖ * b Y) :=
          mul_le_mul (hMa _ hp.2) (h.bound Y hY xw hxw σ hσ p.1 hp.1) (norm_nonneg _)
            ((norm_nonneg _).trans (hMa _ hp.2))
      _ = ‖σ‖ * (Ma * b Y) := by ring
  loc := fun Y hY xw hxw xw' hxw' σ hσ p hp p' hp' h1 h2 h3 => by
    rw [h.loc Y hY xw hxw xw' hxw' σ hσ p.1 hp.1 p'.1 hp'.1 h1.1 h2 h3,
      hloc Y hY p.2 hp.2 p'.2 hp'.2 h1.2]
  zero := fun Y hY xw hxw p hp => by rw [h.zero Y hY xw hxw p.1 hp.1, mul_zero]

end Amp

end LocInt

end Balaban.Fluctuation
