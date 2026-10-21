/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Theorem73
import Mathlib.Tactic.Linarith

/-!
# The composed field in the real domain, with the radius

Theorem 7.3 (real data) with the radius of the composed datum kept explicit: if the real data of
`𝔹'_k` lie in `Ψ̃(𝔹'_k; ν, δ)` with `δ ≤ thm73C1`, and `𝔹 ≺ 𝔹'_k`, then the real part of the
composed field `composeField 𝔹 𝔹'_k a φ' Ψ'`, with `φ'` the complex background `bgFieldC` of the datum,
lies in `Ψ̃(𝔹; ν, C₄ K₁ δ)`, and the composed field is real
(`inPsiTilde_composeField_bgFieldC`). `theorem73_real` states the same inclusion with the radius
hidden in an existential.
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background

namespace Balaban.RootFSpine

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a₁ ν : ℝ}

/-- **The composed field in the real domain with its radius** (Theorem 7.3, real data; Lemma 6.2):
the datum `D'` realizes the real data `(Ψ0, h0) ∈ Ψ̃(𝔹'_k; ν, δ)`, `δ ≤ thm73C1`; then the
composed field of the complex background `bgFieldC` is real, and its real part lies in
`Ψ̃(𝔹; ν, C₄ K₁ δ)` at the same `h0`. -/
theorem inPsiTilde_composeField_bgFieldC (ha₁ : 0 < a₁) (H : BgHyp d L k ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) ν) (h : Precedes G G') {D' : BgData G' N}
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ thm73C1 d L N) {Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h0 : Fin N → ℝ} (hP : InPsiTilde G' ν δ Ψ0 h0)
    (hΨ0 : ∀ x ∈ dataSites G', ∀ i, D'.Ψ x i = (Ψ0 x i : ℂ))
    (hh0 : ∀ x ∈ G'.Ω 1, ∀ i, D'.h x i = (h0 i : ℂ)) :
    (∀ x i, composeField G G' (compWeight L a₁)
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D'.Ψ x i =
      (((composeField G G' (compWeight L a₁)
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D'.Ψ x i).re : ℝ) : ℂ)) ∧
    InPsiTilde G ν (compC4 d * (bgK1 d L N * δ))
      (fun x i => (composeField G G' (compWeight L a₁)
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D'.Ψ x i).re) h0 := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hL2 : 2 ≤ L := by have := H.hL; omega
  obtain ⟨hδ1, -, -, -, -⟩ := thm73_small (L := L) (N := N) hd0 hδ0 hδ
  have hK1 := bgK1_ge_one d L N
  have hD : InDomainR G' ν δ D' := ⟨Ψ0, h0, hP, hΨ0, hh0⟩
  obtain ⟨φ, α, hs, hb, hu, hunit, -, -⟩ := bg_real H' hδ0 hδ1 hD
  obtain ⟨hfC, -⟩ := bgFieldC_eq hs hu
  rw [hfC]
  have hφre : ∀ z i, (φ (z, i)).im = 0 := fun z i => (hunit z).1 i
  have hFB : FieldBounds G' (bgK1 d L N * δ) D'.Ψ φ :=
    fieldBounds_of_bgBounds (fun _ _ _ => rfl) hb hs.1.2
  have hmass := mass_bound_spacing H' hδ0 hδ1 hP hΨ0 hh0 hs
  have hsmall : (4 * d + 6) * (bgK1 d L N * δ) ≤ 1 :=
    (thm73_small (L := L) (N := N) hd0 hδ0 hδ).2.2.2.2
  have hΨreal : ∀ x ∈ dataSites G', ∀ i, (D'.Ψ x i).im = 0 := fun x hx i => by
    rw [hΨ0 x hx i]; simp
  refine ⟨fun x i => ?_, ?_⟩
  · exact congrFun (compVec_isReal h (compWeight L a₁) φ D'.Ψ hφre hΨreal x).eq_ofReal i
  · exact lemma62_core hL2 h ha₁ hK1 hδ0 hsmall H'.mass H'.massLe hP D'.Ψ D'.Ψ_layerConst hΨ0 φ
      hφre hFB (fun z => by
        have e : (fun i => φ (z, i) - D'.h z i) = fun i => φ (z, i) - (h0 i : ℂ) := by
          funext i; rw [hh0 z z.2 i]
        have := hmass z
        rwa [e] at this)

end Balaban.RootFSpine
