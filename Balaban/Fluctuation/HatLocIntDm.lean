/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatDiagContBase
public import Balaban.Fluctuation.InteractionLoc
public import Balaban.Fluctuation.Prop33Agg
public import Balaban.Fluctuation.InteractionAssemble
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Localized expansions with label predicate and diagonal continuity

`LocIntDm P e S XW Rσ 𝒴 T val b AgΘ AgF` is `LocInt` together with

* `dom`: every label `Y ∈ 𝒴` satisfies `P` (for the expansion of Proposition 3.3, `P` is
  "`Y` is a domain of `𝒟_{k+1}`"), and
* `cont`: the diagonal terms `ψ ↦ T_Y(e ψ, e ψ, σ, Θ)` are continuous on the set of `ψ` whose
  diagonal pair is admissible (`DiagCont`).

The combinators of `LocInt` (finite sums, weighted sums, scalar multiples, amplitudes, pullback
along a projection of the directions, restriction of the admissible directions, sums of two
expansions, and the assembly of the four parts of Proposition 3.3) preserve both properties; the
statements are those of the `LocInt` combinators, so that the existing proofs carry over.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Set Metric

section LocIntDm

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {E F : Type*} [TopologicalSpace E] {ι : Type*}

/-- **A localized expansion with domain labels and continuous diagonal terms.** -/
structure LocIntDm (P : ι → Prop) (e : E → F) (S : Set Λ) (XW : Set (F × F)) (Rσ : ℝ)
    (𝒴 : Finset ι) (T : ι → F → F → ℂ → Λ → ℂ) (val : F → F → ℂ → Λ → ℂ) (b : ι → ℝ)
    (AgΘ : ι → Λ → Λ → Prop) (AgF : ι → F → F → Prop) : Prop where
  /-- the localized expansion -/
  loc : LocInt S XW Rσ 𝒴 T val b AgΘ AgF
  /-- the labels satisfy `P` -/
  dom : ∀ Y ∈ 𝒴, P Y
  /-- the diagonal terms are continuous -/
  cont : DiagCont e XW S Rσ 𝒴 T

variable {P : ι → Prop} {e : E → F} {S : Set Λ} {XW : Set (F × F)} {Rσ : ℝ}
  {AgΘ : ι → Λ → Λ → Prop} {AgF : ι → F → F → Prop}

/-- The empty family is a `LocIntDm` for the zero function. -/
theorem locIntDm_empty (T : ι → F → F → ℂ → Λ → ℂ) (b : ι → ℝ) :
    LocIntDm P e S XW Rσ (∅ : Finset ι) T (fun _ _ _ _ => 0) b AgΘ AgF where
  loc := { sum := fun _ _ _ _ _ _ => by simp
           analytic := fun _ hY => absurd hY (Finset.notMem_empty _)
           bound := fun _ hY => absurd hY (Finset.notMem_empty _)
           loc := fun _ hY => absurd hY (Finset.notMem_empty _)
           zero := fun _ hY => absurd hY (Finset.notMem_empty _) }
  dom := fun _ hY => absurd hY (Finset.notMem_empty _)
  cont := fun _ hY => absurd hY (Finset.notMem_empty _)

omit [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] in
theorem DiagCont.mono_XW {𝒴 : Finset ι} {T : ι → F → F → ℂ → Λ → ℂ}
    (h : DiagCont e XW S Rσ 𝒴 T) {XW' : Set (F × F)} (hsub : XW' ⊆ XW) :
    DiagCont e XW' S Rσ 𝒴 T := fun Y hY σ hσ Θ hΘ =>
  (h Y hY σ hσ Θ hΘ).mono fun _ hψ => hsub hψ

variable {𝒴 : Finset ι} {T : ι → F → F → ℂ → Λ → ℂ} {val : F → F → ℂ → Λ → ℂ} {b : ι → ℝ}

/-- Restriction of the set of admissible directions. -/
theorem LocIntDm.mono_XW (h : LocIntDm P e S XW Rσ 𝒴 T val b AgΘ AgF) {XW' : Set (F × F)}
    (hsub : XW' ⊆ XW) : LocIntDm P e S XW' Rσ 𝒴 T val b AgΘ AgF :=
  ⟨h.loc.mono_XW hsub, h.dom, h.cont.mono_XW hsub⟩

/-- Weakening the label predicate. -/
theorem LocIntDm.mono_P (h : LocIntDm P e S XW Rσ 𝒴 T val b AgΘ AgF) {P' : ι → Prop}
    (hP : ∀ Y, P Y → P' Y) : LocIntDm P' e S XW Rσ 𝒴 T val b AgΘ AgF :=
  ⟨h.loc, fun Y hY => hP Y (h.dom Y hY), h.cont⟩

/-- Weakening the bound. -/
theorem LocIntDm.mono (h : LocIntDm P e S XW Rσ 𝒴 T val b AgΘ AgF) {b' : ι → ℝ}
    (hb : ∀ Y, b Y ≤ b' Y) : LocIntDm P e S XW Rσ 𝒴 T val b' AgΘ AgF :=
  ⟨h.loc.mono hb, h.dom, h.cont⟩

/-- Weakening the bound on the labels only. -/
theorem LocIntDm.mono_on (h : LocIntDm P e S XW Rσ 𝒴 T val b AgΘ AgF) {b' : ι → ℝ}
    (hb : ∀ Y ∈ 𝒴, b Y ≤ b' Y) : LocIntDm P e S XW Rσ 𝒴 T val b' AgΘ AgF :=
  ⟨h.loc.mono_on hb, h.dom, h.cont⟩

/-- Changing the expanded function by one that agrees with it on the admissible data. -/
theorem LocIntDm.congr_val (h : LocIntDm P e S XW Rσ 𝒴 T val b AgΘ AgF) {val' : F → F → ℂ → Λ → ℂ}
    (hv : ∀ xw ∈ XW, ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ Θ ∈ S, val' xw.1 xw.2 σ Θ = val xw.1 xw.2 σ Θ) :
    LocIntDm P e S XW Rσ 𝒴 T val' b AgΘ AgF :=
  ⟨h.loc.congr_val hv, h.dom, h.cont⟩

/-- Multiplication by a constant. -/
theorem LocIntDm.smul (h : LocIntDm P e S XW Rσ 𝒴 T val b AgΘ AgF) (c : ℂ) :
    LocIntDm P e S XW Rσ 𝒴 (fun Y x w σ Θ => c * T Y x w σ Θ) (fun x w σ Θ => c * val x w σ Θ)
      (fun Y => ‖c‖ * b Y) AgΘ AgF :=
  ⟨h.loc.smul c, h.dom, fun Y hY σ hσ Θ hΘ => continuousOn_const.mul (h.cont Y hY σ hσ Θ hΘ)⟩

/-- Finite sums of localized expansions over a family of terms `τ ∈ 𝒯`. -/
theorem LocIntDm.finsum [DecidableEq ι] {κ : Type*} (𝒯 : Finset κ) {𝒴 : κ → Finset ι}
    {T : κ → ι → F → F → ℂ → Λ → ℂ} {val : κ → F → F → ℂ → Λ → ℂ} {b : κ → ι → ℝ}
    (h : ∀ τ ∈ 𝒯, LocIntDm P e S XW Rσ (𝒴 τ) (T τ) (val τ) (b τ) AgΘ AgF) :
    LocIntDm P e S XW Rσ (𝒯.biUnion 𝒴)
      (fun Y x w σ Θ => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then T τ Y x w σ Θ else 0)
      (fun x w σ Θ => ∑ τ ∈ 𝒯, val τ x w σ Θ)
      (fun Y => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then b τ Y else 0) AgΘ AgF where
  loc := LocInt.finsum 𝒯 (fun τ hτ => (h τ hτ).loc)
  dom := fun Y hY => by
    obtain ⟨τ, hτ, hYτ⟩ := Finset.mem_biUnion.1 hY
    exact (h τ hτ).dom Y hYτ
  cont := fun Y _ σ hσ Θ hΘ => by
    classical
    refine continuousOn_finsetSum _ fun τ hτ => ?_
    by_cases hY : Y ∈ 𝒴 τ
    · simpa [hY] using (h τ hτ).cont Y hY σ hσ Θ hΘ
    · simp only [hY, ite_false]; exact continuousOn_const

/-- Weighted sum of localized expansions with amplitudes depending on the source `g`. -/
theorem LocIntDm.wsum [DecidableEq ι] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {κ : Type*} (𝒯 : Finset κ) {𝒴 : κ → Finset ι}
    {T : κ → ι → F → F → ℂ → Λ → ℂ} {val : κ → F → F → ℂ → Λ → ℂ} {b : κ → ι → ℝ}
    (h : ∀ τ ∈ 𝒯, LocIntDm P e S XW Rσ (𝒴 τ) (T τ) (val τ) (b τ) AgΘ AgF)
    {SG : Set G} {amp : κ → G → ℂ} (hamp : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (amp τ) SG)
    {AgG : ι → G → G → Prop}
    (hloc : ∀ τ ∈ 𝒯, ∀ Y ∈ 𝒴 τ, ∀ g ∈ SG, ∀ g' ∈ SG, AgG Y g g' → amp τ g = amp τ g')
    {B : ι → ℝ}
    (hB : ∀ Y ∈ 𝒯.biUnion 𝒴, ∀ g ∈ SG,
      ∑ τ ∈ 𝒯, (if Y ∈ 𝒴 τ then ‖amp τ g‖ * b τ Y else 0) ≤ B Y) :
    LocIntDm P e (S ×ˢ SG) XW Rσ (𝒯.biUnion 𝒴)
      (fun Y x w σ p => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then amp τ p.2 * T τ Y x w σ p.1 else 0)
      (fun x w σ p => ∑ τ ∈ 𝒯, amp τ p.2 * val τ x w σ p.1)
      B (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF where
  loc := LocInt.wsum 𝒯 (fun τ hτ => (h τ hτ).loc) hamp hloc hB
  dom := fun Y hY => by
    obtain ⟨τ, hτ, hYτ⟩ := Finset.mem_biUnion.1 hY
    exact (h τ hτ).dom Y hYτ
  cont := fun Y _ σ hσ p hp => by
    classical
    refine continuousOn_finsetSum _ fun τ hτ => ?_
    by_cases hY : Y ∈ 𝒴 τ
    · simp only [hY, ite_true]
      exact continuousOn_const.mul ((h τ hτ).cont Y hY σ hσ p.1 hp.1)
    · simp only [hY, ite_false]; exact continuousOn_const

/-- Multiplication by an analytic amplitude depending on an extra parameter. -/
theorem LocIntDm.mulAmp (h : LocIntDm P e S XW Rσ 𝒴 T val b AgΘ AgF)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] {SG : Set G} {amp : G → ℂ} {Ma : ℝ}
    (hamp : AnalyticOnNhd ℂ amp SG) (hMa : ∀ g ∈ SG, ‖amp g‖ ≤ Ma) {AgG : ι → G → G → Prop}
    (hloc : ∀ Y ∈ 𝒴, ∀ g ∈ SG, ∀ g' ∈ SG, AgG Y g g' → amp g = amp g') :
    LocIntDm P e (S ×ˢ SG) XW Rσ 𝒴 (fun Y x w σ p => amp p.2 * T Y x w σ p.1)
      (fun x w σ p => amp p.2 * val x w σ p.1) (fun Y => Ma * b Y)
      (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF :=
  ⟨h.loc.mulAmp hamp hMa hloc, h.dom, fun Y hY σ hσ p hp =>
    continuousOn_const.mul (h.cont Y hY σ hσ p.1 hp.1)⟩

/-- The sum of two localized expansions with the same labels and bounds added. -/
theorem LocIntDm.add₂ [DecidableEq ι] {𝒴' : Finset ι} {T' : ι → F → F → ℂ → Λ → ℂ}
    {val' : F → F → ℂ → Λ → ℂ} {b' : ι → ℝ}
    (h : LocIntDm P e S XW Rσ 𝒴 T val b AgΘ AgF) (h' : LocIntDm P e S XW Rσ 𝒴' T' val' b' AgΘ AgF) :
    LocIntDm P e S XW Rσ (𝒴 ∪ 𝒴')
      (fun Y x w σ Θ => (if Y ∈ 𝒴 then T Y x w σ Θ else 0) +
        (if Y ∈ 𝒴' then T' Y x w σ Θ else 0))
      (fun x w σ Θ => val x w σ Θ + val' x w σ Θ)
      (fun Y => (if Y ∈ 𝒴 then b Y else 0) + (if Y ∈ 𝒴' then b' Y else 0)) AgΘ AgF where
  loc := h.loc.add₂ h'.loc
  dom := fun Y hY => by
    rcases Finset.mem_union.1 hY with hY | hY
    · exact h.dom Y hY
    · exact h'.dom Y hY
  cont := fun Y _ σ hσ Θ hΘ => by
    classical
    refine ContinuousOn.add ?_ ?_
    · by_cases hY : Y ∈ 𝒴
      · simpa [hY] using h.cont Y hY σ hσ Θ hΘ
      · simp only [hY, ite_false]; exact continuousOn_const
    · by_cases hY : Y ∈ 𝒴'
      · simpa [hY] using h'.cont Y hY σ hσ Θ hΘ
      · simp only [hY, ite_false]; exact continuousOn_const

/-- Pulling back along a projection of the directions; `e'` is the diagonal embedding on the
bigger space with `π ∘ e' = e`. -/
theorem LocIntDm.comap (h : LocIntDm P e S XW Rσ 𝒴 T val b AgΘ AgF) {F' : Type*} (π : F' → F)
    {XW' : Set (F' × F')} (hXW : ∀ xw ∈ XW', (π xw.1, π xw.2) ∈ XW)
    {AgF' : ι → F' → F' → Prop} (hAg : ∀ Y a a', AgF' Y a a' → AgF Y (π a) (π a'))
    {e' : E → F'} (he : ∀ ψ, π (e' ψ) = e ψ) :
    LocIntDm P e' S XW' Rσ 𝒴 (fun Y x w σ Θ => T Y (π x) (π w) σ Θ)
      (fun x w σ Θ => val (π x) (π w) σ Θ) b AgΘ AgF' where
  loc := h.loc.comap π hXW hAg
  dom := h.dom
  cont := fun Y hY σ hσ Θ hΘ => by
    refine ((h.cont Y hY σ hσ Θ hΘ).mono fun ψ hψ => ?_).congr fun ψ _ => by simp only [he]
    have := hXW _ hψ
    simpa [DiagDom, he] using this

section Assemble

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
variable [DecidableEq ι]

/-- **The assembly of the four parts with a differentiability clause.**  As `LocIntDm.assemble`, together
with the differentiability of the assembled term along the paths `u` (`P' u`) at a fixed datum, when the
four parts have it (the parts `V`, `E` at `u`, the parts `F`, `M` at `u`). -/
theorem LocIntDm.assemble_ray {SG : Set G} {XWV XWE XWF XWM : Set (F × F)}
    {𝒴V 𝒴E 𝒴F 𝒴M : Finset ι} {TV TE : ι → F → F → ℂ → Λ → ℂ}
    {TF TM : ι → F → F → ℂ → Λ × G → ℂ} {valV valE : F → F → ℂ → Λ → ℂ}
    {valF valM : F → F → ℂ → Λ × G → ℂ} {bV bE bF bM : ι → ℝ}
    {AgG : ι → G → G → Prop}
    (hV : LocIntDm P e S XWV Rσ 𝒴V TV valV bV AgΘ AgF)
    (hE : LocIntDm P e S XWE Rσ 𝒴E TE valE bE AgΘ AgF)
    (hF : LocIntDm P e (S ×ˢ SG) XWF Rσ 𝒴F TF valF bF
      (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF)
    (hM : LocIntDm P e (S ×ˢ SG) XWM Rσ 𝒴M TM valM bM
      (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF)
    (cV cE cF cM : ℂ) (hbV : ∀ Y, 0 ≤ bV Y) (hbE : ∀ Y, 0 ≤ bE Y) (hbF : ∀ Y, 0 ≤ bF Y)
    (hbM : ∀ Y, 0 ≤ bM Y)
    {P' : (ℂ → F) → Prop} {s : Set ℂ}
    (rV : ∀ Y (u : ℂ → F), P' u → ∀ Θ ∈ S, DifferentiableOn ℂ (fun z => TV Y (u z) (u z) 1 Θ) s)
    (rE : ∀ Y (u : ℂ → F), P' u → ∀ Θ ∈ S, DifferentiableOn ℂ (fun z => TE Y (u z) (u z) 1 Θ) s)
    (rF : ∀ Y (u : ℂ → F), P' u → ∀ p ∈ S ×ˢ SG,
      DifferentiableOn ℂ (fun z => TF Y (u z) (u z) 1 p) s)
    (rM : ∀ Y (u : ℂ → F), P' u → ∀ p ∈ S ×ˢ SG,
      DifferentiableOn ℂ (fun z => TM Y (u z) (u z) 1 p) s) :
    ∃ (𝒴 : Finset ι) (T : ι → (F × F) → (F × F) → ℂ → Λ × G → ℂ) (b : ι → ℝ),
      (∀ Y, b Y ≤ ‖cV‖ * bV Y + ‖cE‖ * bE Y + ‖cF‖ * bF Y + ‖cM‖ * bM Y) ∧
      LocIntDm P (fun ψ => (e ψ, e ψ)) (S ×ˢ SG)
        {xw : (F × F) × (F × F) | (xw.1.1, xw.2.1) ∈ XWV ∧ (xw.1.1, xw.2.1) ∈ XWE ∧
          (xw.1.2, xw.2.2) ∈ XWF ∧ (xw.1.2, xw.2.2) ∈ XWM} Rσ 𝒴 T
        (fun x w σ p => cV * valV x.1 w.1 σ p.1 + cE * valE x.1 w.1 σ p.1 +
          cF * valF x.2 w.2 σ p + cM * valM x.2 w.2 σ p) b
        (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2)
        (fun Y a a' => AgF Y a.1 a'.1 ∧ AgF Y a.2 a'.2) ∧
      ∀ Y (u : ℂ → F), P' u → ∀ p ∈ S ×ˢ SG,
        DifferentiableOn ℂ (fun z => T Y (u z, u z) (u z, u z) 1 p) s := by
  classical
  have hV1 := hV.mulAmp (SG := SG) (amp := fun _ => (1 : ℂ)) (Ma := 1)
    (analyticOnNhd_const) (fun _ _ => by simp) (AgG := AgG) (fun _ _ _ _ _ _ _ => rfl)
  have hE1 := hE.mulAmp (SG := SG) (amp := fun _ => (1 : ℂ)) (Ma := 1)
    (analyticOnNhd_const) (fun _ _ => by simp) (AgG := AgG) (fun _ _ _ _ _ _ _ => rfl)
  have hV2 := (hV1.smul cV).comap (F' := F × F) Prod.fst
    (XW' := {xw : (F × F) × (F × F) | (xw.1.1, xw.2.1) ∈ XWV ∧ (xw.1.1, xw.2.1) ∈ XWE ∧
          (xw.1.2, xw.2.2) ∈ XWF ∧ (xw.1.2, xw.2.2) ∈ XWM}) (fun xw hxw => hxw.1)
    (AgF' := fun Y a a' => AgF Y a.1 a'.1 ∧ AgF Y a.2 a'.2) (fun Y a a' h => h.1)
    (e' := fun ψ => (e ψ, e ψ)) (fun _ => rfl)
  have hE2 := (hE1.smul cE).comap (F' := F × F) Prod.fst
    (XW' := {xw : (F × F) × (F × F) | (xw.1.1, xw.2.1) ∈ XWV ∧ (xw.1.1, xw.2.1) ∈ XWE ∧
          (xw.1.2, xw.2.2) ∈ XWF ∧ (xw.1.2, xw.2.2) ∈ XWM}) (fun xw hxw => hxw.2.1)
    (AgF' := fun Y a a' => AgF Y a.1 a'.1 ∧ AgF Y a.2 a'.2) (fun Y a a' h => h.1)
    (e' := fun ψ => (e ψ, e ψ)) (fun _ => rfl)
  have hF2 := (hF.smul cF).comap (F' := F × F) Prod.snd
    (XW' := {xw : (F × F) × (F × F) | (xw.1.1, xw.2.1) ∈ XWV ∧ (xw.1.1, xw.2.1) ∈ XWE ∧
          (xw.1.2, xw.2.2) ∈ XWF ∧ (xw.1.2, xw.2.2) ∈ XWM}) (fun xw hxw => hxw.2.2.1)
    (AgF' := fun Y a a' => AgF Y a.1 a'.1 ∧ AgF Y a.2 a'.2) (fun Y a a' h => h.2)
    (e' := fun ψ => (e ψ, e ψ)) (fun _ => rfl)
  have hM2 := (hM.smul cM).comap (F' := F × F) Prod.snd
    (XW' := {xw : (F × F) × (F × F) | (xw.1.1, xw.2.1) ∈ XWV ∧ (xw.1.1, xw.2.1) ∈ XWE ∧
          (xw.1.2, xw.2.2) ∈ XWF ∧ (xw.1.2, xw.2.2) ∈ XWM}) (fun xw hxw => hxw.2.2.2)
    (AgF' := fun Y a a' => AgF Y a.1 a'.1 ∧ AgF Y a.2 a'.2) (fun Y a a' h => h.2)
    (e' := fun ψ => (e ψ, e ψ)) (fun _ => rfl)
  have h12 := hV2.add₂ hE2
  have h123 := h12.add₂ hF2
  have h1234 := h123.add₂ hM2
  refine ⟨_, _, _, fun Y => ?_, h1234.congr_val ?_, ?_⟩
  · simp only [one_mul]
    have n1 := mul_nonneg (norm_nonneg cV) (hbV Y)
    have n2 := mul_nonneg (norm_nonneg cE) (hbE Y)
    have n3 := mul_nonneg (norm_nonneg cF) (hbF Y)
    have n4 := mul_nonneg (norm_nonneg cM) (hbM Y)
    split_ifs <;> linarith
  · intro xw hxw σ hσ p hp
    simp only [one_mul]
  · intro Y u hu p hp
    have key : ∀ (c : Prop) [Decidable c] (f : ℂ → ℂ), (c → DifferentiableOn ℂ f s) →
        DifferentiableOn ℂ (fun z => if c then f z else 0) s := fun c _ f h => by
      by_cases hc : c
      · simpa only [hc, ite_true] using h hc
      · simpa only [hc, ite_false] using differentiableOn_const (0 : ℂ)
    have hV3 : DifferentiableOn ℂ (fun z => cV * (1 * TV Y (u z) (u z) 1 p.1)) s :=
      ((rV Y u hu p.1 hp.1).const_mul 1).const_mul cV
    have hE3 : DifferentiableOn ℂ (fun z => cE * (1 * TE Y (u z) (u z) 1 p.1)) s :=
      ((rE Y u hu p.1 hp.1).const_mul 1).const_mul cE
    have hF3 : DifferentiableOn ℂ (fun z => cF * TF Y (u z) (u z) 1 p) s :=
      (rF Y u hu p hp).const_mul cF
    have hM3 : DifferentiableOn ℂ (fun z => cM * TM Y (u z) (u z) 1 p) s :=
      (rM Y u hu p hp).const_mul cM
    refine DifferentiableOn.add ?_ ?_
    · apply key; intro _
      refine DifferentiableOn.add ?_ ?_
      · apply key; intro _
        refine DifferentiableOn.add ?_ ?_
        · apply key; intro _; exact hV3
        · apply key; intro _; exact hE3
      · apply key; intro _; exact hF3
    · apply key; intro _; exact hM3

/-- **The assembly of the four parts** (`locInt_assemble`) with labels and diagonal continuity. -/
theorem LocIntDm.assemble {SG : Set G} {XWV XWE XWF XWM : Set (F × F)}
    {𝒴V 𝒴E 𝒴F 𝒴M : Finset ι} {TV TE : ι → F → F → ℂ → Λ → ℂ}
    {TF TM : ι → F → F → ℂ → Λ × G → ℂ} {valV valE : F → F → ℂ → Λ → ℂ}
    {valF valM : F → F → ℂ → Λ × G → ℂ} {bV bE bF bM : ι → ℝ}
    {AgG : ι → G → G → Prop}
    (hV : LocIntDm P e S XWV Rσ 𝒴V TV valV bV AgΘ AgF)
    (hE : LocIntDm P e S XWE Rσ 𝒴E TE valE bE AgΘ AgF)
    (hF : LocIntDm P e (S ×ˢ SG) XWF Rσ 𝒴F TF valF bF
      (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF)
    (hM : LocIntDm P e (S ×ˢ SG) XWM Rσ 𝒴M TM valM bM
      (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF)
    (cV cE cF cM : ℂ) (hbV : ∀ Y, 0 ≤ bV Y) (hbE : ∀ Y, 0 ≤ bE Y) (hbF : ∀ Y, 0 ≤ bF Y)
    (hbM : ∀ Y, 0 ≤ bM Y) :
    ∃ (𝒴 : Finset ι) (T : ι → (F × F) → (F × F) → ℂ → Λ × G → ℂ) (b : ι → ℝ),
      (∀ Y, b Y ≤ ‖cV‖ * bV Y + ‖cE‖ * bE Y + ‖cF‖ * bF Y + ‖cM‖ * bM Y) ∧
      LocIntDm P (fun ψ => (e ψ, e ψ)) (S ×ˢ SG)
        {xw : (F × F) × (F × F) | (xw.1.1, xw.2.1) ∈ XWV ∧ (xw.1.1, xw.2.1) ∈ XWE ∧
          (xw.1.2, xw.2.2) ∈ XWF ∧ (xw.1.2, xw.2.2) ∈ XWM} Rσ 𝒴 T
        (fun x w σ p => cV * valV x.1 w.1 σ p.1 + cE * valE x.1 w.1 σ p.1 +
          cF * valF x.2 w.2 σ p + cM * valM x.2 w.2 σ p) b
        (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2)
        (fun Y a a' => AgF Y a.1 a'.1 ∧ AgF Y a.2 a'.2) := by
  classical
  exact (LocIntDm.assemble_ray hV hE hF hM cV cE cF cM hbV hbE hbF hbM (P' := fun _ => False)
    (s := ∅) (fun _ _ h => h.elim) (fun _ _ h => h.elim) (fun _ _ h => h.elim)
    (fun _ _ h => h.elim)).imp fun _ => Exists.imp fun _ => Exists.imp fun _ h => ⟨h.1, h.2.1⟩

/-- **Adding a `Θ`-only part to a localized expansion in `(Θ, g)`** (`LocIntDm.addLift`), together
with the differentiability of the sum along the paths `u` (`P u`) at a fixed datum, when both parts
have it. -/
theorem LocIntDm.addLift_ray {SG : Set G} {F' : Type*} {XW : Set (F' × F')} {XWν : Set (F × F)}
    {𝒴 𝒴ν : Finset ι} {T : ι → F' → F' → ℂ → Λ × G → ℂ} {Tν : ι → F → F → ℂ → Λ → ℂ}
    {val : F' → F' → ℂ → Λ × G → ℂ} {valν : F → F → ℂ → Λ → ℂ} {b bν : ι → ℝ}
    {AgG : ι → G → G → Prop} {AgF' : ι → F' → F' → Prop} {e' : E → F'} (π : F' → F)
    (hXW : ∀ xw ∈ XW, (π xw.1, π xw.2) ∈ XWν)
    (hAg : ∀ Y a a', AgF' Y a a' → AgF Y (π a) (π a'))
    (he : ∀ ψ, π (e' ψ) = e ψ)
    (hν : LocIntDm P e S XWν Rσ 𝒴ν Tν valν bν AgΘ AgF)
    (hL : LocIntDm P e' (S ×ˢ SG) XW Rσ 𝒴 T val b
      (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF')
    (c : ℂ) {P' : (ℂ → F') → Prop} {s : Set ℂ}
    (rL : ∀ Y (u : ℂ → F'), P' u → ∀ p ∈ S ×ˢ SG,
      DifferentiableOn ℂ (fun z => T Y (u z) (u z) 1 p) s)
    (rν : ∀ Y (u : ℂ → F'), P' u → ∀ Θ ∈ S,
      DifferentiableOn ℂ (fun z => Tν Y (π (u z)) (π (u z)) 1 Θ) s) :
    ∃ T' : ι → F' → F' → ℂ → Λ × G → ℂ,
      LocIntDm P e' (S ×ˢ SG) XW Rσ (𝒴 ∪ 𝒴ν) T'
        (fun x w σ p => val x w σ p + c * valν (π x) (π w) σ p.1)
        (fun Y => (if Y ∈ 𝒴 then b Y else 0) + (if Y ∈ 𝒴ν then ‖c‖ * (1 * bν Y) else 0))
        (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF' ∧
      ∀ Y (u : ℂ → F'), P' u → ∀ p ∈ S ×ˢ SG,
        DifferentiableOn ℂ (fun z => T' Y (u z) (u z) 1 p) s := by
  have h1 := hν.mulAmp (SG := SG) (amp := fun _ => (1 : ℂ)) (Ma := 1)
    (analyticOnNhd_const) (fun _ _ => by simp) (AgG := AgG) (fun _ _ _ _ _ _ _ => rfl)
  have h2 := (h1.smul c).comap (F' := F') π (XW' := XW) hXW (AgF' := AgF') hAg he
  refine ⟨_, (hL.add₂ h2).congr_val (fun xw hxw σ hσ p hp => by simp only [one_mul]), ?_⟩
  intro Y u hu p hp
  have key : ∀ (c : Prop) [Decidable c] (f : ℂ → ℂ), (c → DifferentiableOn ℂ f s) →
      DifferentiableOn ℂ (fun z => if c then f z else 0) s := fun c _ f h => by
    by_cases hc : c
    · simpa only [hc, ite_true] using h hc
    · simpa only [hc, ite_false] using differentiableOn_const (0 : ℂ)
  refine DifferentiableOn.add ?_ ?_
  · apply key; intro _; exact rL Y u hu p hp
  · apply key; intro _
    exact ((rν Y u hu p.1 hp.1).const_mul 1).const_mul c

/-- **Adding a `Θ`-only part to a localized expansion in `(Θ, g)`** (`LocInt.addLift`) with
labels and diagonal continuity. -/
theorem LocIntDm.addLift {SG : Set G} {F' : Type*} {XW : Set (F' × F')} {XWν : Set (F × F)}
    {𝒴 𝒴ν : Finset ι} {T : ι → F' → F' → ℂ → Λ × G → ℂ} {Tν : ι → F → F → ℂ → Λ → ℂ}
    {val : F' → F' → ℂ → Λ × G → ℂ} {valν : F → F → ℂ → Λ → ℂ} {b bν : ι → ℝ}
    {AgG : ι → G → G → Prop} {AgF' : ι → F' → F' → Prop} {e' : E → F'} (π : F' → F)
    (hXW : ∀ xw ∈ XW, (π xw.1, π xw.2) ∈ XWν)
    (hAg : ∀ Y a a', AgF' Y a a' → AgF Y (π a) (π a'))
    (he : ∀ ψ, π (e' ψ) = e ψ)
    (hν : LocIntDm P e S XWν Rσ 𝒴ν Tν valν bν AgΘ AgF)
    (hL : LocIntDm P e' (S ×ˢ SG) XW Rσ 𝒴 T val b
      (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF')
    (c : ℂ) :
    ∃ T' : ι → F' → F' → ℂ → Λ × G → ℂ,
      LocIntDm P e' (S ×ˢ SG) XW Rσ (𝒴 ∪ 𝒴ν) T'
        (fun x w σ p => val x w σ p + c * valν (π x) (π w) σ p.1)
        (fun Y => (if Y ∈ 𝒴 then b Y else 0) + (if Y ∈ 𝒴ν then ‖c‖ * (1 * bν Y) else 0))
        (fun Y p p' => AgΘ Y p.1 p'.1 ∧ AgG Y p.2 p'.2) AgF' := by
  classical
  obtain ⟨T', hT'⟩ := LocIntDm.addLift_ray π hXW hAg he hν hL c (P' := fun _ => False) (s := ∅)
    (fun _ _ h => h.elim) (fun _ _ h => h.elim)
  exact ⟨T', hT'.1⟩

end Assemble

end LocIntDm

end Balaban.Fluctuation
