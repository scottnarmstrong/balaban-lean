/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionLoc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Assembling the four parts of the localized interaction

The localized interaction `𝒰_{t,u}` of (3.3) is the sum of the potential part, the `δ𝓔`-part
(both built from the pair `(x₀, w)` of the parameter `t`) and the source parts `⟨g, δφ⟩` and the
`𝓜`-terms (built from the pair of the parameter `u`).  `locInt_assemble` adds four localized
expansions over the common data space `Θ × g`, with constant prefactors, pulling the first two back
along the first projection and the last two along the second.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Set Metric

section Assemble

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
variable {F : Type*} {ι : Type*} [DecidableEq ι]

theorem locInt_assemble {S : Set Λ} {SG : Set G} {Rσ : ℝ}
    {XWV XWE : Set (F × F)} {XWF XWM : Set (F × F)}
    {𝒴V 𝒴E 𝒴F 𝒴M : Finset ι} {TV TE : ι → F → F → ℂ → Λ → ℂ}
    {TF TM : ι → F → F → ℂ → Λ × G → ℂ} {valV valE : F → F → ℂ → Λ → ℂ}
    {valF valM : F → F → ℂ → Λ × G → ℂ} {bV bE bF bM : ι → ℝ}
    {AgΘ : ι → Λ → Λ → Prop} {AgG : ι → G → G → Prop} {AgF : ι → F → F → Prop}
    (hV : LocInt S XWV Rσ 𝒴V TV valV bV AgΘ AgF) (hE : LocInt S XWE Rσ 𝒴E TE valE bE AgΘ AgF)
    (hF : LocInt (S ×ˢ SG) XWF Rσ 𝒴F TF valF bF (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF)
    (hM : LocInt (S ×ˢ SG) XWM Rσ 𝒴M TM valM bM (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF)
    (cV cE cF cM : ℂ) (hbV : ∀ Y, 0 ≤ bV Y) (hbE : ∀ Y, 0 ≤ bE Y) (hbF : ∀ Y, 0 ≤ bF Y)
    (hbM : ∀ Y, 0 ≤ bM Y) :
    ∃ (𝒴 : Finset ι) (T : ι → (F × F) → (F × F) → ℂ → Λ × G → ℂ) (b : ι → ℝ),
      (∀ Y, b Y ≤ ‖cV‖ * bV Y + ‖cE‖ * bE Y + ‖cF‖ * bF Y + ‖cM‖ * bM Y) ∧
      LocInt (S ×ˢ SG)
        {xw : (F × F) × (F × F) | (xw.1.1, xw.2.1) ∈ XWV ∧ (xw.1.1, xw.2.1) ∈ XWE ∧
          (xw.1.2, xw.2.2) ∈ XWF ∧ (xw.1.2, xw.2.2) ∈ XWM} Rσ 𝒴 T
        (fun x w σ p => cV * valV x.1 w.1 σ p.1 + cE * valE x.1 w.1 σ p.1 +
          cF * valF x.2 w.2 σ p + cM * valM x.2 w.2 σ p) b
        (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2)
        (fun Y a a' => AgF Y a.1 a'.1 ∧ AgF Y a.2 a'.2) := by
  classical
  -- lift the first two parts to `Θ × g` with the amplitude `1`
  have hV1 := hV.mulAmp (SG := SG) (amp := fun _ => (1 : ℂ)) (Ma := 1)
    (analyticOnNhd_const) (fun _ _ => by simp) (AgG := AgG) (fun _ _ _ _ _ _ _ => rfl)
  have hE1 := hE.mulAmp (SG := SG) (amp := fun _ => (1 : ℂ)) (Ma := 1)
    (analyticOnNhd_const) (fun _ _ => by simp) (AgG := AgG) (fun _ _ _ _ _ _ _ => rfl)
  -- pull back along the projections of the pairs of directions
  have hV2 := (hV1.smul cV).comap (F' := F × F) Prod.fst
    (XW' := {xw : (F × F) × (F × F) | (xw.1.1, xw.2.1) ∈ XWV ∧ (xw.1.1, xw.2.1) ∈ XWE ∧
          (xw.1.2, xw.2.2) ∈ XWF ∧ (xw.1.2, xw.2.2) ∈ XWM}) (fun xw hxw => hxw.1)
    (AgF' := fun Y a a' => AgF Y a.1 a'.1 ∧ AgF Y a.2 a'.2) (fun Y a a' h => h.1)
  have hE2 := (hE1.smul cE).comap (F' := F × F) Prod.fst
    (XW' := {xw : (F × F) × (F × F) | (xw.1.1, xw.2.1) ∈ XWV ∧ (xw.1.1, xw.2.1) ∈ XWE ∧
          (xw.1.2, xw.2.2) ∈ XWF ∧ (xw.1.2, xw.2.2) ∈ XWM}) (fun xw hxw => hxw.2.1)
    (AgF' := fun Y a a' => AgF Y a.1 a'.1 ∧ AgF Y a.2 a'.2) (fun Y a a' h => h.1)
  have hF2 := (hF.smul cF).comap (F' := F × F) Prod.snd
    (XW' := {xw : (F × F) × (F × F) | (xw.1.1, xw.2.1) ∈ XWV ∧ (xw.1.1, xw.2.1) ∈ XWE ∧
          (xw.1.2, xw.2.2) ∈ XWF ∧ (xw.1.2, xw.2.2) ∈ XWM}) (fun xw hxw => hxw.2.2.1)
    (AgF' := fun Y a a' => AgF Y a.1 a'.1 ∧ AgF Y a.2 a'.2) (fun Y a a' h => h.2)
  have hM2 := (hM.smul cM).comap (F' := F × F) Prod.snd
    (XW' := {xw : (F × F) × (F × F) | (xw.1.1, xw.2.1) ∈ XWV ∧ (xw.1.1, xw.2.1) ∈ XWE ∧
          (xw.1.2, xw.2.2) ∈ XWF ∧ (xw.1.2, xw.2.2) ∈ XWM}) (fun xw hxw => hxw.2.2.2)
    (AgF' := fun Y a a' => AgF Y a.1 a'.1 ∧ AgF Y a.2 a'.2) (fun Y a a' h => h.2)
  have h12 := hV2.add₂ hE2
  have h123 := h12.add₂ hF2
  have h1234 := h123.add₂ hM2
  refine ⟨_, _, _, fun Y => ?_, h1234.congr_val ?_⟩
  · simp only [one_mul]
    have n1 := mul_nonneg (norm_nonneg cV) (hbV Y)
    have n2 := mul_nonneg (norm_nonneg cE) (hbE Y)
    have n3 := mul_nonneg (norm_nonneg cF) (hbF Y)
    have n4 := mul_nonneg (norm_nonneg cM) (hbM Y)
    split_ifs <;> linarith
  · intro xw hxw σ hσ p hp
    simp only [one_mul]

end Assemble

end Balaban.Fluctuation
