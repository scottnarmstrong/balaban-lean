/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusTranslate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Recentring: the coefficient correspondence of the translated functions

`evTerm_boxMap_of_diameter` (`TwoTorusTranslate`) asks for the correspondence of the coefficients of
the recentred functions `F ∘ parEquiv` and `F' ∘ parEquiv` on the translated parameter sets.  The
coefficients of a relabelled function are the coefficients of the original function at the
relabelled family (`coef_relabel`), and the connected families of the translated set are the
relabelled connected families (`connFams_relabel`).  Hence that hypothesis is equivalent to the
correspondence of the coefficients of `F` and `F'` themselves, for the families of `X₁`, `S'` that
correspond under the recentred transport map `φ x = bm (x + tA) - tB`
(`coef_recentred_of_coef`); this is the hypothesis of `evTerm_boxMap_of_width` for `φ` in place of
the transport map, and does not mention the translated sets, the relabellings or the position of
`X₁`.  `evTerm_boxMap_of_diameter_of_coef` is `evTerm_boxMap_of_diameter` with it.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section Recentre

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl

/-- **The coefficient correspondence of the recentred functions from that of the originals.**
If the coefficients of `F u` and `F' u'` agree on the families that correspond under the recentred
transport map `φ x = bm (x + tA) - tB` (the families of `X₁` and `S'`), then the coefficients of the
recentred functions `F ∘ parEquiv_{tA}`, `F' ∘ parEquiv_{tB}` agree on the families of the
translated sets that correspond under `bm`. -/
theorem coef_recentred_of_coef {U U' : Type*} {m₀ : ℕ} {ρ : ℝ} (hρ : 1 < ρ)
    (hk : 1 ≤ k + 1) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    {X₁ Y : Set (CTorus d L N₁ m₁ (k + 1))}
    {S' : Set (CTorus d L N₁' m₁ (k + 1))}
    {F : U → (ParIdx (GA) X₁ → ℂ) → ℂ} {F' : U' → (ParIdx (GB) S' → ℂ) → ℂ} {u : U} {u' : U'}
    (hF : AnalyticOnNhd ℂ (F u) (polydisc (0 : ParIdx (GA) X₁ → ℂ) (fun _ => ρ)))
    (hF' : AnalyticOnNhd ℂ (F' u') (polydisc (0 : ParIdx (GB) S' → ℂ) (fun _ => ρ)))
    {FA : U → (ParIdx (GA) ((Equiv.addRight tA) '' X₁) → ℂ) → ℂ}
    {FB : U' → (ParIdx (GB) ((Equiv.addRight tB) '' S') → ℂ) → ℂ}
    (hFA : FA = fun u s => F u (s ∘ parEquiv
      (DecEquiv.CoverSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) tA
        (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ)))
      (DecEquiv.PolymerSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) hN tA htA) rfl))
    (hFB : FB = fun u s => F' u (s ∘ parEquiv
      (DecEquiv.CoverSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) tB
        (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ)))
      (DecEquiv.PolymerSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) hN' tB htB) rfl))
    (hcoef : ∀ C ∈ connFams (fun i : ParIdx (GA) X₁ => i.1.1) (GA) m₀ X₁ Y,
      ∀ C' : Finset (ParIdx (GB) S'),
        (∀ i ∈ C, ∃ i' ∈ C', i'.1.1 = Prod.map id (fun x => bm (x + tA) - tB) i.1.1) →
        (∀ i' ∈ C', ∃ i ∈ C, i'.1.1 = Prod.map id (fun x => bm (x + tA) - tB) i.1.1) →
        coef (F' u') C' = coef (F u) C) :
    ∀ C ∈ connFams (fun i : ParIdx (GA) ((Equiv.addRight tA) '' X₁) => i.1.1) (GA) m₀
        ((Equiv.addRight tA) '' X₁) ((Equiv.addRight tA) '' Y),
      ∀ C' : Finset (ParIdx (GB) ((Equiv.addRight tB) '' S')),
        (∀ i ∈ C, ∃ i' ∈ C', i'.1.1 = Prod.map id bm i.1.1) →
        (∀ i' ∈ C', ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1) →
        coef (FB u') C' = coef (FA u) C := by
  have hGA : IsLevel (GA) (k + 1) := isLevel_levelGS (by omega) le_rfl
  have hGB : IsLevel (GB) (k + 1) := isLevel_levelGS (by omega) le_rfl
  have hSA := DecEquiv.LatSymm.ofTranslateLevel hGA tA
    (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ))
  set CSA := DecEquiv.CoverSymm.ofTranslate hGA tA
    (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ)) with hCSA
  set PA := DecEquiv.PolymerSymm.ofTranslate hGA hN tA htA with hPA
  set CSB := DecEquiv.CoverSymm.ofTranslate hGB tB
    (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ)) with hCSB
  set PB := DecEquiv.PolymerSymm.ofTranslate hGB hN' tB htB with hPB
  set κA := parEquiv CSA PA (X₁ := X₁) (X₁' := (Equiv.addRight tA) '' X₁) rfl with hκA
  set κB := parEquiv CSB PB (X₁ := S') (X₁' := (Equiv.addRight tB) '' S') rfl with hκB
  intro C hC C' h1 h2
  rw [connFams_relabel (fun i : ParIdx (GA) X₁ => i.1.1)
    (fun i : ParIdx (GA) ((Equiv.addRight tA) '' X₁) => i.1.1) κA (fun _ => rfl)
    (fun i => i.1.2) PA hSA X₁ Y] at hC
  obtain ⟨C0, hC0, rfl⟩ := Finset.mem_map.1 hC
  have hAn : AnalyticOnNhd ℂ (FA u) (polydisc (0 : ParIdx (GA) ((Equiv.addRight tA) '' X₁) → ℂ)
      (fun _ => ρ)) := by
    rw [hFA]; exact analyticOnNhd_comp_relabel _ hF
  have hBn : AnalyticOnNhd ℂ (FB u') (polydisc (0 : ParIdx (GB) ((Equiv.addRight tB) '' S') → ℂ)
      (fun _ => ρ)) := by
    rw [hFB]; exact analyticOnNhd_comp_relabel _ hF'
  have e1 : coef (FA u) (C0.map κA.toEmbedding) = coef (F u) C0 :=
    coef_relabel hρ κA hF hAn (by intro s _; rw [hFA]) C0
  set C0' := C'.map κB.symm.toEmbedding with hC0'
  have hCe : C0'.map κB.toEmbedding = C' := by
    ext j
    constructor
    · intro h
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 h
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 ha
      simpa only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply] using hb
    · intro h
      exact Finset.mem_map.2 ⟨κB.symm j, Finset.mem_map.2 ⟨j, h, rfl⟩, by simp only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply]⟩
  have e2 : coef (FB u') C' = coef (F' u') C0' := by
    rw [← hCe]
    exact coef_relabel hρ κB hF' hBn (by intro s _; rw [hFB]) C0'
  simp only [Function.Embedding.coeFn_mk] at h1 h2 ⊢
  rw [e1, e2]
  have key : ∀ (i : ParIdx (GA) X₁) (i' : ParIdx (GB) S'),
      (κB i').1.1 = Prod.map id bm (κA i).1.1 →
      i'.1.1 = Prod.map id (fun x => bm (x + tA) - tB) i.1.1 := by
    intro i i' he
    have hb : (κB i').1.1 = CSB.τ i'.1.1 := rfl
    have ha : (κA i).1.1 = CSA.τ i.1.1 := rfl
    rw [ha, hb] at he
    change (i'.1.1.1, i'.1.1.2 + tB) = (i.1.1.1, bm (i.1.1.2 + tA)) at he
    have he' := Prod.ext_iff.1 he
    exact Prod.ext he'.1 (eq_sub_of_add_eq he'.2)
  refine hcoef C0 hC0 C0' ?_ ?_
  · intro i hi
    obtain ⟨i', hi', he⟩ := h1 (κA i) (Finset.mem_map_of_mem _ hi)
    refine ⟨κB.symm i', Finset.mem_map.2 ⟨i', hi', rfl⟩, key i _ ?_⟩
    rw [Equiv.apply_symm_apply]; exact he
  · intro i' hi'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi'
    obtain ⟨i1, hi1, he⟩ := h2 j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hi1
    refine ⟨i, hi, key i _ ?_⟩
    simpa only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply] using he

/-- **The torus clause for a polymer of small diameter anywhere on the torus, with the coefficient
correspondence of the original functions** (item 24, part 2).  `evTerm_boxMap_of_diameter`, with its
hypothesis `_hcoef` on the recentred functions replaced by the correspondence of the coefficients of
`F u` and `F' u'` on the families that correspond under the recentred map
`φ x = bm (x + tA) - tB` (`coef_recentred_of_coef`). -/
theorem evTerm_boxMap_of_diameter_of_coef {U U' : Type*} {m₀ D : ℕ} {ρ : ℝ} (hρ : 1 < ρ)
    (hd : 0 < d) (hL : 2 ≤ L)
    (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 25 * D + 25 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 25 * D + 25 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))}
    (hbox : ∃ b, box b (L * cellSide L m₀ m₁ (k + 1)) ⊆ X₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hD : ∀ x ∈ X₁, ∀ y ∈ X₁ ∪ Y, ∀ μ, |(x μ - y μ).valMinAbs| ≤ D) :
    ∃ z : Fin d → ℤ, (∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ) ∧
      (∀ x ∈ X₁ ∪ Y, InBox d (D + (D + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1))
        (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) ∧
      ∃ (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
        (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
        (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val),
      tA = (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) ∧
      tB = (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) ∧
      ∀ {S' : Set (CTorus d L N₁' m₁ (k + 1))}
    (_hS' : S' = (fun x => bm (x + tA) - tB) '' X₁)
      {F : U → (ParIdx (GA) X₁ → ℂ) → ℂ} {F' : U' → (ParIdx (GB) S' → ℂ) → ℂ} {u : U} {u' : U'}
    (_hF : AnalyticOnNhd ℂ (F u) (polydisc (0 : ParIdx (GA) X₁ → ℂ) (fun _ => ρ)))
    (_hF' : AnalyticOnNhd ℂ (F' u') (polydisc (0 : ParIdx (GB) S' → ℂ) (fun _ => ρ)))
    {FA : U → (ParIdx (GA) ((Equiv.addRight tA) '' X₁) → ℂ) → ℂ}
    {FB : U' → (ParIdx (GB) ((Equiv.addRight tB) '' S') → ℂ) → ℂ}
    (_hFA : FA = fun u s => F u (s ∘ parEquiv
      (DecEquiv.CoverSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) tA
        (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ)))
      (DecEquiv.PolymerSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) hN tA htA) rfl))
    (_hFB : FB = fun u s => F' u (s ∘ parEquiv
      (DecEquiv.CoverSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) tB
        (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ)))
      (DecEquiv.PolymerSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) hN' tB htB) rfl))
    (_hcoef : ∀ C ∈ connFams (fun i : ParIdx (GA) X₁ => i.1.1) (GA) m₀ X₁ Y,
      ∀ C' : Finset (ParIdx (GB) S'),
        (∀ i ∈ C, ∃ i' ∈ C', i'.1.1 = Prod.map id (fun x => bm (x + tA) - tB) i.1.1) →
        (∀ i' ∈ C', ∃ i ∈ C, i'.1.1 = Prod.map id (fun x => bm (x + tA) - tB) i.1.1) →
        coef (F' u') C' = coef (F u) C),

      evTerm (fun i : ParIdx (GB) S' => i.1.1) (GB) m₀ S' F'
        ((fun x => bm (x + tA) - tB) '' Y) u' =
      evTerm (fun i : ParIdx (GA) X₁ => i.1.1) (GA) m₀ X₁ F Y u := by
  obtain ⟨z, hz, hbx, tA, tB, htA, htB, rfl, rfl, H⟩ := evTerm_boxMap_of_diameter (U := U) (U' := U')
    (ρ := ρ) (D := D) hρ hd hL hm₀ hm₁ hN hN' hn hn' hbox hD
  refine ⟨z, hz, hbx, _, _, htA, htB, rfl, rfl, ?_⟩
  intro S' hS' F F' u u' hF hF' FA FB hFA hFB hcoef
  exact H hS' hF hF' hFA hFB (coef_recentred_of_coef hρ (by omega) hN hN' _ _ htA htB hF hF' hFA hFB hcoef)

end Recentre

end Balaban.Polymer.TwoTorusStep
