/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.Mayer
import Balaban.Polymer.TwoTorusE1Coef
import Mathlib.Tactic.Linarith

/-!
# Transport of the local terms of the Mayer gas

`PY_mayer_transport`: if a map of blocks `σ` is injective on a set `Y`, a relation `Rel` between
configurations of two systems carries integrals of functions of the blocks of `Z ⊆ Y`, and the
terms of the two systems agree on related configurations (`H'_{σ t} = H_t`), then the local terms of
the polymer gases of the Mayer activities of the two systems agree, `P'(σ '' Y) = P(Y)`. The polymers
inside `Y` and `σ '' Y` correspond (`PY_transport`), as do their connected families
(`polyAct_transport`). This is the unmarked case of `Gst_transport`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.Polymer

open Balaban.Polymer.TwoTorusStep

section Transport

variable {B B' : Type*} [Fintype B] [Fintype B'] [DecidableEq B']
  {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)] {Ω' : B' → Type*} [∀ b, MeasurableSpace (Ω' b)]
  (μ : ∀ b, Measure (Ω b)) (μ' : ∀ b, Measure (Ω' b))


/-- **Transport of the local terms of the Mayer gas.**  Let `σ` map the blocks of a first system to
those of a second, injectively on the set `Y`, and let a relation `Rel` between configurations
carry integrals of functions of the blocks of `Z ⊆ Y`. If the terms `H_t`, `t ⊆ Y`, of the first
system and `H'_{σ t}` of the second agree on related configurations, then the local terms of the
two gases at `Y` and `σ '' Y` agree. -/
theorem PY_mayer_transport (σ : B → B') (Y : Finset B) (hσ : Set.InjOn σ (Y : Set B))
    (Hf : NePoly B → (∀ b, Ω b) → ℂ) (Hf' : NePoly B' → (∀ b, Ω' b) → ℂ)
    (Rel : (∀ b, Ω b) → (∀ b, Ω' b) → Prop)
    (hint : ∀ Z ⊆ Y, ∀ (F : (∀ b, Ω b) → ℂ) (F' : (∀ b, Ω' b) → ℂ), DepOn Z F →
      (∀ Φ Φ', Rel Φ Φ' → F' Φ' = F Φ) →
        ∫ Φ', F' Φ' ∂(Measure.pi μ') = ∫ Φ, F Φ ∂(Measure.pi μ))
    (hdep : ∀ t : NePoly B, DepOn t.1 (Hf t))
    (hH : ∀ t : NePoly B, t.1 ⊆ Y → ∀ Φ Φ', Rel Φ Φ' →
      Hf' ⟨t.1.image σ, t.2.image σ⟩ Φ' = Hf t Φ) :
    PY (shareBlock (Subtype.val : NePoly B' → Finset B')) Subtype.val
        (mayerK μ' (fun X : NePoly B' => X.1) Hf') (Y.image σ) =
      PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
        (mayerK μ (fun X : NePoly B => X.1) Hf) Y := by
  let img : NePoly B → NePoly B' := fun t => ⟨t.1.image σ, t.2.image σ⟩
  have himg_inj : ∀ t₁ t₂ : NePoly B, t₁.1 ⊆ Y → t₂.1 ⊆ Y → img t₁ = img t₂ → t₁ = t₂ :=
    fun t₁ t₂ h₁ h₂ h => Subtype.ext (eq_of_image_eq_of_injOn hσ h₁ h₂ (congrArg Subtype.val h))
  -- the activities of the polymers inside `Y` agree
  have hK : ∀ x : NePoly B, x.1 ⊆ Y →
      mayerK μ' (fun X : NePoly B' => X.1) Hf' (img x) =
        mayerK μ (fun X : NePoly B => X.1) Hf x := by
    intro x hx
    unfold mayerK
    refine hint x.1 hx _ _ (depOn_mayerAct hdep x) (fun Φ Φ' hR => ?_)
    unfold mayerAct
    refine polyAct_transport σ img x (img x) rfl (hσ.mono (by exact_mod_cast hx))
      (fun t _ => by rfl) (fun t₁ t₂ h₁ h₂ h => himg_inj t₁ t₂ (h₁.trans hx) (h₂.trans hx) h)
      (fun t' ht' => ?_) _ _ (fun t ht => ?_)
    · obtain ⟨t, htx, hte⟩ := exists_nePoly_image t' ht'
      exact ⟨t, htx, Subtype.ext hte⟩
    · show Complex.exp (Hf' (img t) Φ') - 1 = Complex.exp (Hf t Φ) - 1
      rw [hH t (ht.trans hx) Φ Φ' hR]
  have hbij : Function.Bijective (fun x : {x : NePoly B // x.1 ⊆ Y} =>
      (⟨img x.1, Finset.image_subset_image x.2⟩ : {x' : NePoly B' // x'.1 ⊆ Y.image σ})) := by
    refine ⟨fun x₁ x₂ h => Subtype.ext (himg_inj _ _ x₁.2 x₂.2 (congrArg Subtype.val h)),
      fun x' => ?_⟩
    obtain ⟨t, htS, hte⟩ := exists_nePoly_image x'.1 x'.2
    exact ⟨⟨t, htS⟩, Subtype.ext (Subtype.ext hte)⟩
  let Ψ := Equiv.ofBijective _ hbij
  refine PY_transport (inc := shareBlock (Subtype.val : NePoly B → Finset B))
    (inc' := shareBlock (Subtype.val : NePoly B' → Finset B'))
    (supp := Subtype.val) (supp' := Subtype.val) Y (Y.image σ) σ hσ
    (fun b' => by simp [Finset.mem_image]) Ψ (fun x b' => ?_) (fun x y => ?_) (fun x => ?_)
  · show b' ∈ x.1.1.image σ ↔ _
    exact Finset.mem_image
  · rw [lnk_shareBlock, lnk_shareBlock]
    exact not_disjoint_image_iff_of_injOn hσ x.2 y.2
  · exact hK x.1 x.2

end Transport

end Balaban.Polymer
