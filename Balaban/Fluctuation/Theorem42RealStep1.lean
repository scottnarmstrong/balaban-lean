/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.Lift
public import Balaban.Background.CompositionDomain
public import Balaban.Background.Def5
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 4.2, Step 1 for the real step (FLUCTUATION.md §4.2, LFR Lemma II.2.5 (c), BG (6.2))

For generating sets `𝔹^loc ≺ 𝔹^∂` at level `k+1` (`Precedes G G'`) with the mixed lifts `ψ̃` of the
same `(ψ_k, ϑ, h)`:

* `stepComposed`: the datum `ψ(𝔹^loc, 𝔹^∂; ψ̃)` of (6.2), `composeData` of the boundary
  background `φ^∂ = bgFieldC G' D'`;
* `stepComposed_eq_on`: on a set `E` where the layers of `𝔹^loc` and `𝔹^∂` coincide
  (`E_{Z'}`, Lemma II.2.5 (c)) the composed datum equals `ψ̃`: `δΨ = 0` on `E`;
* `stepComposed_h`: the two data have the same `h`;
* `stepComposed_bg`: for data in the domain `𝒟`, `φ(𝔹^loc; ψ(𝔹^loc, 𝔹^∂; ψ̃)) = φ^∂|_{Ω₁(𝔹^loc)}`
  (`isEL_compose`, uniqueness `theorem72`);
* `real_step1`: **`φ^∂ - φ^loc = φ(𝔹^loc; ψ̃ + δΨ) - φ(𝔹^loc; ψ̃)`** with `δΨ = 0` on `E`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField

section Step1

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L N₀ (k + 1) ϱ} {G' : GeneratingSet d L N₀ (k + 1) ϱ'}

/-- **The datum of `𝔹^loc` obtained from the boundary background by the composition (6.2)**:
`ψ(𝔹^loc, 𝔹^∂; ψ̃)`, i.e. `composeData` of the small solution `φ^∂ = bgFieldC` of `𝔹^∂`. -/
noncomputable def stepComposed (hprec : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (D' : BgData G' N) :
    BgData G N :=
  composeData hprec a (bgFieldC G' a ν (bgC0 d L N) D') D'

theorem layerIndex_eq_of_agree {E : Set (Torus d (N₀ * L ^ (k + 1)))}
    (hE : ∀ x ∈ E, ∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ G.Ω n ↔ x ∈ G'.Ω n))
    {x : Torus d (N₀ * L ^ (k + 1))} (hx : x ∈ E) (hxΩ : x ∈ G.Ω 1) :
    G.layerIndex x = G'.layerIndex x := by
  obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hxΩ
  have h1 : x ∈ G'.Ω (G.layerIndex x) := (hE x hx _ hn1 hnk).1 (G.mem_layer.1 hxl).1
  have h2 : x ∉ G'.Ω (G.layerIndex x + 1) := by
    intro h
    by_cases hlt : G.layerIndex x + 1 ≤ k + 1
    · exact (G.mem_layer.1 hxl).2 ((hE x hx _ (by omega) hlt).2 h)
    · have hh : G.layerIndex x = k + 1 := by omega
      rw [hh] at h
      have := G'.top
      rw [this] at h
      exact Finset.notMem_empty _ h
  have : x ∈ G'.layer (G.layerIndex x) := G'.mem_layer.2 ⟨h1, h2⟩
  exact (G'.layerIndex_eq hn1 hnk this).symm

theorem composeField_eq_of_agree (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (Ψ' : Torus d (N₀ * L ^ (k + 1)) → Fin N → ℂ) {x : Torus d (N₀ * L ^ (k + 1))}
    (hx : x ∈ G.Ω 1) (hli : G.layerIndex x = G'.layerIndex x) (ha : a (G.layerIndex x) ≠ 0)
    (i : Fin N) : composeField G G' a φ' Ψ' x i = Ψ' x i := by
  rw [composeField_of_mem a φ' Ψ' hx]
  rw [← hli]
  have hb : blockMean G' (G.layerIndex x) (fun y => svec G' φ' y i) x =
      blockMean G (G.layerIndex x) (fun y => svec G' φ' y i) x := rfl
  rw [hb]
  have hL : ((L : ℝ) ^ G.layerIndex x) ^ 2 ≠ 0 := by
    have : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    positivity
  have hc : (a (G.layerIndex x) / a (G.layerIndex x) *
      (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G.layerIndex x) ^ 2) : ℝ) = 1 := by
    rw [div_self ha, div_self hL, one_mul]
  rw [hc]
  push_cast
  ring

variable {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))}
  (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω) (hG : G.Ω (k + 1) ⊆ Ω) (hG' : G'.Ω (k + 1) ⊆ Ω)
  (ψ : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ)
  (ϑ : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ)

include hΩ hG hG' in
/-- **The data change vanishes where the layers agree** (LFR Lemma II.2.5 (c)): on a set `E` on
which the layers of `𝔹^loc` and `𝔹^∂` coincide, the composed datum (6.2) equals the lifted datum
`ψ̃` of `𝔹^loc`, for every weights with `a_n ≠ 0`. -/
theorem stepComposed_eq_on (hprec : Precedes G G') {a : ℕ → ℝ}
    (ha : ∀ j, 1 ≤ j → j ≤ k + 1 → a j ≠ 0) {ν : ℝ}
    {E : Set (Torus d (N₀ * L ^ (k + 1)))}
    (hE : ∀ x ∈ E, ∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ G.Ω n ↔ x ∈ G'.Ω n))
    {x : Torus d (N₀ * L ^ (k + 1))} (hx : x ∈ E) (i : Fin N) :
    (stepComposed hprec a ν (liftMixed G' hΩ hG' ψ ϑ h)).Ψ x i =
      (liftMixed G hΩ hG ψ ϑ h).Ψ x i := by
  classical
  show composeField G G' a _ (liftMixed G' hΩ hG' ψ ϑ h).Ψ x i = _
  by_cases hxΩ : x ∈ G.Ω 1
  · have hxΩ' : x ∈ G'.Ω 1 := (hE x hx 1 le_rfl (by omega)).1 hxΩ
    have hli := layerIndex_eq_of_agree hE hx hxΩ
    have hn := G.layerIndex_spec hxΩ
    rw [composeField_eq_of_agree a _ _ hxΩ hli (ha _ hn.1 (by omega))]
    rw [liftMixed_Ψ G' hΩ hG' ψ ϑ h ((mem_dataSites G').2 (Or.inl hxΩ')),
      liftMixed_Ψ G hΩ hG ψ ϑ h ((mem_dataSites G).2 (Or.inl hxΩ))]
  · by_cases hxc : x ∈ collar G
    · have hxΩ' : x ∉ G'.Ω 1 := fun hh => hxΩ ((hE x hx 1 le_rfl (by omega)).2 hh)
      rw [composeField_of_collar a _ _ hxc]
      unfold barField
      simp only [hxΩ', ↓reduceDIte]
      have hc' : x ∈ dataSites G' := (mem_dataSites G').2 (Or.inr (by
        obtain ⟨-, y, hy, hadj⟩ := (mem_collar G).1 hxc
        exact (mem_collar G').2 ⟨hxΩ', y, hprec.mem_Ω1 hy, hadj⟩))
      rw [liftMixed_Ψ G' hΩ hG' ψ ϑ h hc',
        liftMixed_Ψ G hΩ hG ψ ϑ h ((mem_dataSites G).2 (Or.inr hxc))]
    · have hnd : x ∉ dataSites G := fun hh => by
        rcases (mem_dataSites G).1 hh with h1 | h1
        · exact hxΩ h1
        · exact hxc h1
      rw [composeField_of_not_mem a _ _ hnd, (liftMixed G hΩ hG ψ ϑ h).Ψ_zero x hnd]
      rfl

include hΩ hG hG' in
/-- The composed datum has the same `h` as the lifted datum of `𝔹^loc`
("the two constructions use the same `h`", FLUCTUATION §4.2 Step 1). -/
theorem stepComposed_h (hprec : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (x : Torus d (N₀ * L ^ (k + 1))) :
    (stepComposed hprec a ν (liftMixed G' hΩ hG' ψ ϑ h)).h x = (liftMixed G hΩ hG ψ ϑ h).h x := by
  classical
  funext i
  show (if x ∈ G.Ω 1 then (liftMixed G' hΩ hG' ψ ϑ h).h x i else 0 : ℂ) = _
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, ↓reduceIte]
    rw [liftMixed_h G' hΩ hG' ψ ϑ h (hprec.mem_Ω1 hx), liftMixed_h G hΩ hG ψ ϑ h hx]
  · simp only [hx, ↓reduceIte]
    rw [(liftMixed G hΩ hG ψ ϑ h).h_zero x hx]
    rfl

/-- **Composition identity for the background** (BG Theorem 6.1 (ii), identities):
for `𝔹^loc ≺ 𝔹^∂` and data in the domain `𝒟`, the background of `𝔹^loc` at the composed datum is the
restriction of the background of `𝔹^∂`: `φ(𝔹^loc; ψ(𝔹^loc, 𝔹^∂; ψ̃)) = φ^∂|_{Ω₁(𝔹^loc)}`. -/
theorem stepComposed_bg (hprec : Precedes G G') {a : ℕ → ℝ} {ν : ℝ}
    (H : BgHyp d L (k + 1) ϱ a ν) (H' : BgHyp d L (k + 1) ϱ' a ν) (D' : BgData G' N)
    (hD' : InUnionDomainC G' (bgC0 d L N) (bgC1 d L N) ν D')
    (hDu : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (stepComposed hprec a ν D')) :
    bgFieldC G a ν (bgC0 d L N) (stepComposed hprec a ν D') =
      hprec.restrictφ (bgFieldC G' a ν (bgC0 d L N) D') := by
  have ha : ∀ j, 1 ≤ j → j ≤ k + 1 → a j ≠ 0 := fun j h1 h2 => by
    have := (H.weights j h1 h2).1
    intro h0; rw [h0] at this; norm_num at this
  obtain ⟨-, hS, -⟩ := theorem72 H' hD'
  obtain ⟨hU, hS0, -⟩ := theorem72 H hDu
  have hU' : ∀ φ₁ φ₂ α₁ α₂, IsSmallSolution G a ν (bgC0 d L N) (stepComposed hprec a ν D') φ₁ α₁ →
      IsSmallSolution G a ν (bgC0 d L N) (stepComposed hprec a ν D') φ₂ α₂ →
      φ₁ = φ₂ ∧ α₁ = α₂ := by
    intro φ₁ φ₂ α₁ α₂ h1 h2
    have e1 := hU.unique (y₁ := (φ₁, α₁)) (y₂ := (φ₂, α₂)) h1 h2
    exact ⟨congrArg Prod.fst e1, congrArg Prod.snd e1⟩
  exact (compose_eq_of_unique hprec a ha ν D' hS hU' hS0).1

include hΩ hG hG' in
/-- **Theorem 4.2, Step 1, for the real step** (FLUCTUATION §4.2, LFR Lemma II.2.5 (c)):
let `𝔹^loc ≺ 𝔹^∂` be generating sets whose layers coincide on the set `E` (= `E_{Z'}`), with the
lifts `ψ̃` (mixed lift of `ψ_k, ϑ, h`) on both, and data in the domain `𝒟`.  Then there is a data
change `δΨ` vanishing on `E` such that the composed datum is `ψ̃ + δΨ` (same `h`), and
`φ^∂ - φ^loc = φ(𝔹^loc; ψ̃ + δΨ) - φ(𝔹^loc; ψ̃)` on `Ω₁(𝔹^loc)`. -/
theorem real_step1 (hprec : Precedes G G') {a : ℕ → ℝ} {ν : ℝ}
    (H : BgHyp d L (k + 1) ϱ a ν) (H' : BgHyp d L (k + 1) ϱ' a ν)
    {E : Set (Torus d (N₀ * L ^ (k + 1)))}
    (hE : ∀ x ∈ E, ∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ G.Ω n ↔ x ∈ G'.Ω n))
    (hD' : InUnionDomainC G' (bgC0 d L N) (bgC1 d L N) ν (liftMixed G' hΩ hG' ψ ϑ h))
    (hDu : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν
      (stepComposed hprec a ν (liftMixed G' hΩ hG' ψ ϑ h))) :
    ∃ δΨ : Torus d (N₀ * L ^ (k + 1)) → Fin N → ℂ,
      (∀ x ∈ E, ∀ i, δΨ x i = 0) ∧
      (∀ x i, (stepComposed hprec a ν (liftMixed G' hΩ hG' ψ ϑ h)).Ψ x i =
        (liftMixed G hΩ hG ψ ϑ h).Ψ x i + δΨ x i) ∧
      (∀ x i, (stepComposed hprec a ν (liftMixed G' hΩ hG' ψ ϑ h)).h x i =
        (liftMixed G hΩ hG ψ ϑ h).h x i) ∧
      (∀ z : G.Ω 1, ∀ i,
        bgFieldC G' a ν (bgC0 d L N) (liftMixed G' hΩ hG' ψ ϑ h) (hprec.incl z, i) -
          bgFieldC G a ν (bgC0 d L N) (liftMixed G hΩ hG ψ ϑ h) (z, i) =
        bgFieldC G a ν (bgC0 d L N) (stepComposed hprec a ν (liftMixed G' hΩ hG' ψ ϑ h)) (z, i) -
          bgFieldC G a ν (bgC0 d L N) (liftMixed G hΩ hG ψ ϑ h) (z, i)) := by
  have ha : ∀ j, 1 ≤ j → j ≤ k + 1 → a j ≠ 0 := fun j h1 h2 => by
    have := (H.weights j h1 h2).1
    intro h0; rw [h0] at this; norm_num at this
  refine ⟨fun x i => (stepComposed hprec a ν (liftMixed G' hΩ hG' ψ ϑ h)).Ψ x i -
    (liftMixed G hΩ hG ψ ϑ h).Ψ x i, fun x hx i => ?_, fun x i => by ring,
    fun x i => congrFun (stepComposed_h hΩ hG hG' ψ ϑ h hprec a ν x) i, fun z i => ?_⟩
  · simp only [stepComposed_eq_on hΩ hG hG' ψ ϑ h hprec ha hE hx i, sub_self]
  · have := stepComposed_bg hprec H H' (liftMixed G' hΩ hG' ψ ϑ h) hD' hDu
    have e := congrFun this (z, i)
    rw [e]
    rfl

end Step1
end Balaban.Fluctuation
