/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsTiltLabels
public import Balaban.Inhabited.ActivityFamilyAnalytic
public import Balaban.Fluctuation.SourceFamilyRelative

/-!
# Locality of the observable activity family in the datum and the source

The source `g` enters the observable only through the activity family, whose direct terms are
evaluated at the parameter `(raw datum, g / β)`.  This file proves that the activity of a label
with domain `Y` reads the raw datum only on the thickening `thickSet Y` and the source only on `Y`.

* `physInclScaled_physAgΘ`: two parameters whose raw data agree on `thickSet Y` and whose sources
  agree on `Y` have scaled inclusions in the relation `physAgΘ S Y`.
* `labelActFamilyOn_local_scaled`: the activity of a label with domain `y.1` of the family
  `labelActFamilyOn S m₀ (physInclScaled N S c) …` is the same at two such parameters.
* `physAct_H_local`, `physAct_H_local_of_family`: the same for each coefficient of `physAct`
  (the zero-source summands read only the raw datum on `thickSet Y`).
* `physActObs_H_local`, `tiltActObs_H_local`: the extension by zero to the observable labels and
  the scalar tilt.
-/

@[expose] public section

namespace Balaban.Inhabited

open MeasureTheory Metric Balaban Balaban.Fluctuation Balaban.Localization Balaban.Polymer
  Balaban.SmallField Balaban.Multiscale Balaban.Background

section Scaled

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **Scaled agreement.**  If the raw data of two parameters agree on `thickSet Y` and their
sources agree on `Y`, the scaled inclusions `(r, g) ↦ (r, c g)` satisfy `physAgΘ S Y`. -/
theorem physInclScaled_physAgΘ (c : ℂ) {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    {e e' : physParam N S}
    (hr : agreeOn (thickSet S.G' Y) (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
      (e'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))
    (hg : ∀ x ∈ Y, e.2 x = e'.2 x) :
    physAgΘ S Y (physInclScaled N S c e) (physInclScaled N S c e') := by
  refine ⟨hr, fun x hx => ?_⟩
  simp [physInclScaled_apply, hg x hx]

end Scaled

section Activity

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {F' : Type} {hp : 0 < S.p₁}
  {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a : ℝ}
  {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
  {SΛ : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
  {XW : Set (F' × F')}
  {val : F' → F' → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N ×
    (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
  (c : ℂ)
  {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val (physAgΘ S) AgF} {V : Set (physParam N S)}
  (hF : DirectTermsFamilyOn S m₀ (physInclScaled N S c) I V)
  (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
  {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)

/-- **Locality of the activity family in the pair (raw datum, source).**  For a label with domain
`y.1`, two parameters of `V` whose raw data agree on `thickSet y.1` and whose sources agree on
`y.1` have the same label activity, for every `u`. -/
theorem labelActFamilyOn_local_scaled {e e' : physParam N S} (he : e ∈ V) (he' : e' ∈ V)
    (y : {Y // Y ∈ I.𝒴})
    (hr : agreeOn (thickSet S.G' y.1) (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
      (e'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))
    (hg : ∀ x ∈ y.1, e.2 x = e'.2 x) (u : ℂ) :
    (labelActFamilyOn S m₀ (physInclScaled N S c) I hF hN hρ hRσ hεU hκ0 hKc e u).H y =
      (labelActFamilyOn S m₀ (physInclScaled N S c) I hF hN hρ hRσ hεU hκ0 hKc e' u).H y := by
  refine labelActFamilyOn_local S m₀ (physInclScaled N S c) hF hN hρ hRσ hεU hκ0 hKc he he'
    y.1 ?_ u y subset_rfl
  intro Y _ hYy
  exact physInclScaled_physAgΘ S c
    (agreeOn_mono (thickSet_mono hYy) hr) (fun x hx => hg x (hYy hx))

end Activity

section Phys

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ} {Lb : Type} [Fintype Lb]
variable {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
  Set.univ Lb} {εH κH κ0 Kc : ℝ}
  {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ → Type}
  [∀ b, MeasurableSpace (Ωb b)] {E₁ E₂ : Type*} [Zero E₂]
  (A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)

/-- **Locality of the coefficients of `physAct`.**  If the label `y` of the family is local for the
pairs `(e.1, 0), (e'.1, 0)` (zero source) and `e, e'`, then both kinds of coefficient of `physAct`
at `e` and `e'` agree. -/
theorem physAct_H_local {e e' : E₁ × E₂} (t : ℂ) (y : Lb ⊕ Lb)
    (h0 : ∀ u, ∀ z, y = Sum.inl z → (A (e.1, 0) u).H z = (A (e'.1, 0) u).H z)
    (h1 : ∀ z, y = Sum.inr z → (A e t).H z = (A e' t).H z) :
    (physAct A e t).H y = (physAct A e' t).H y := by
  rcases y with z | z
  · funext Φ
    rw [physAct_H_inl, physAct_H_inl, h0 1 z rfl, h0 t z rfl]
  · exact h1 z rfl

variable {hN : L ^ m₀ ∣ N₁} {hκ0 : aEnt d L + 1 ≤ κ0} {hεH : 0 ≤ εH}
  {𝒴obs : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {hdj : ∀ Y ∈ 𝒴obs, IsDj m₀ (k + 1) Y}
  {Kobs : ℝ} {hK : Kc + Kc + K0 d L κ0 + K0 d L κ0 ≤ Kobs}

/-- **The extension to the observable labels.**  The coefficients on the labels of `Lab.sum Lab`
are those of `physAct`; the new labels have zero activity at every parameter. -/
theorem physActObs_H_local {e e' : E₁ × E₂} (t : ℂ) (y : ObsLb (Lb ⊕ Lb) m₀ 𝒴obs)
    (hy : ∀ z, y = Sum.inl (Sum.inl z) →
      (physAct A e t).H z = (physAct A e' t).H z) :
    (physActObs A hN hκ0 hεH hdj hK e t).H y = (physActObs A hN hκ0 hεH hdj hK e' t).H y := by
  by_cases h : ∃ z, y = Sum.inl (Sum.inl z)
  · obtain ⟨z, rfl⟩ := h
    funext Φ
    rw [physActObs_H_inl, physActObs_H_inl]
    exact congrFun (hy z rfl) Φ
  · push Not at h
    funext Φ
    rw [physActObs_H_new A hN hκ0 hεH hdj hK e t y h,
      physActObs_H_new A hN hκ0 hεH hdj hK e' t y h]

/-- **The tilt.**  The tilt is a scalar factor independent of `e`, so its coefficients are local
exactly as those of `physActObs`. -/
theorem tiltActObs_H_local {e e' : E₁ × E₂} (Rg : ℝ) (hR : 0 ≤ Rg) (𝒰 : Set ℂ) (t σ : ℂ)
    (y : ObsLb (Lb ⊕ Lb) m₀ 𝒴obs)
    (hy : (physActObs A hN hκ0 hεH hdj hK e t).H y =
      (physActObs A hN hκ0 hεH hdj hK e' t).H y) :
    (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 e t σ).H y =
      (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 e' t σ).H y := by
  funext Φ
  rw [tiltActObs_H, tiltActObs_H, hy]

end Phys


section Combined

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {F' : Type} {hp : 0 < S.p₁}
  {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a : ℝ}
  {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
  {SΛ : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
  {XW : Set (F' × F')}
  {val : F' → F' → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N ×
    (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
  (c : ℂ)
  {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val (physAgΘ S) AgF} {V : Set (physParam N S)}
  (hF : DirectTermsFamilyOn S m₀ (physInclScaled N S c) I V)
  (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
  {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)

/-- **Coefficients of `physAct` of the analytic family.**  Let `A = labelActFamilyOn …` and let
`e, e'` be two parameters such that `e, e'` and the zero-source parameters `(e.1, 0), (e'.1, 0)`
lie in `V`.  If the raw data agree on `thickSet y.1` and the sources agree on `y.1`, then the
coefficients of `physAct A` at the label `y` (either summand) agree for every `t`. -/
theorem physAct_H_local_of_family {e e' : physParam N S} (he : e ∈ V) (he' : e' ∈ V)
    (he0 : ((e.1, 0) : physParam N S) ∈ V) (he0' : ((e'.1, 0) : physParam N S) ∈ V)
    (t : ℂ) (y : {Y // Y ∈ I.𝒴})
    (hr : agreeOn (thickSet S.G' y.1) (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
      (e'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))
    (hg : ∀ x ∈ y.1, e.2 x = e'.2 x) (z : {Y // Y ∈ I.𝒴} ⊕ {Y // Y ∈ I.𝒴})
    (hz : z = Sum.inl y ∨ z = Sum.inr y) :
    (physAct (labelActFamilyOn S m₀ (physInclScaled N S c) I hF hN hρ hRσ hεU hκ0 hKc) e t).H z =
      (physAct (labelActFamilyOn S m₀ (physInclScaled N S c) I hF hN hρ hRσ hεU hκ0 hKc)
        e' t).H z := by
  rcases hz with rfl | rfl
  · exact physAct_H_local _ t _
      (fun u w hw => by
        cases hw
        exact labelActFamilyOn_local_scaled S m₀ c hF hN hρ hRσ hεU hκ0 hKc he0 he0' y hr
          (fun _ _ => rfl) u)
      (fun w hw => by cases hw)
  · exact physAct_H_local _ t _ (fun u w hw => by cases hw)
      (fun w hw => by
        cases hw
        exact labelActFamilyOn_local_scaled S m₀ c hF hN hρ hRσ hεU hκ0 hKc he he' y hr hg t)


end Combined

end Balaban.Inhabited
