/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionEngine
public import Balaban.Localization.DecEquivCoef
public import Balaban.Localization.DecEquivReal

/-!
# Symmetries of the expansion terms of the interaction (FLUCTUATION.md Proposition 3.3, symmetry clause)

`expansion_of_AE_evTerm` is `expansion_of_AE` with the term map exposed: the terms are
`Ev Y = evTerm c Gp m₀ X₁ FF Y`, the sum over the connected families of the coefficients `FF_C`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix
  Balaban.Fluctuation

section Core

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- **`expansion_of_AE` with the term map exposed**: the terms are `evTerm … FF Y`. -/
theorem expansion_of_AE_evTerm (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {B' : Set (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    {FF : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) →
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) → ℂ}
    (hana : AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
        (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
        (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) => FF p.1 p.2)
      ((XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ B') ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ)))
    (hbd : ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps ×ˢ B',
      ∀ s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ)
        (fun _ => Real.exp κ),
      ‖FF u s‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    (hloc : LocalityAEOn (Real.exp κ) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ B')
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ K)))
      (fun C u u' => agreeOn (thickSet Gp (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ K)) C)) u.1 u'.1 ∧
        ∀ y ∈ psiThick (compY
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y) FF) :
    (∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ B',
        FF u 1 = ∑ Y ∈ polymerDomains
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X), evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
            Gp m₀ (X1 Gp m₀ j 𝒦X) FF Y u) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ B',
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ B',
        agreeOn (thickSet Gp Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) FF Y u =
        evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) FF Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ B',
        ‖evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) FF Y u‖ ≤
          Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ
        (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) FF Y) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ B')) := by
  classical
  have hc : ∀ i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)), (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) i ∈ cubeIdx Gp := fun i => i.1.2
  have hcinj : Function.Injective (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) := fun i i' h => Subtype.ext (Subtype.ext h)
  have hdisj : ∀ i, Disjoint (Pset m₁ ((fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) i)) (X1 Gp m₀ j 𝒦X) := fun i => hX₁ ▸ i.2
  have hrefl : ∀ (C : Finset (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)))) (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)), u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps ×ˢ B' →
      (fun C u u' => agreeOn (N := N) (thickSet Gp (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C))
        u.1 u'.1 ∧ ∀ y ∈ psiThick (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y)
        C u u := fun C u _ => ⟨agreeOn_refl _ u.1, fun _ _ => rfl⟩
  have hlink : ∀ (C : Finset (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)))) (u u' : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)), (agreeOn (N := N) (thickSet Gp (Ysites Gp m₀ (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (X1 Gp m₀ j 𝒦X) C)) u.1 u'.1 ∧
        ∀ y ∈ psiThick (Ysites Gp m₀ (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (X1 Gp m₀ j 𝒦X) C), u.2 y = u'.2 y) →
      (agreeOn (N := N) (thickSet Gp (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C)) u.1 u'.1 ∧
        ∀ y ∈ psiThick (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y) := by
    intro C u u' h
    have hsub : compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C ⊆
        Ysites Gp m₀ (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (X1 Gp m₀ j 𝒦X) C := by
      have e1 : compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C =
          compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (X1 Gp m₀ j 𝒦X) C :=
        congrArg (fun S => compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) S C) hX₁
      rw [e1]; exact compY_subset_Ysites hcov.hU hcov.hN hc _ C
    exact ⟨agreeOn_mono (thickSet_mono hsub) h.1, fun y hy => h.2 y (psiThick_mono hsub hy)⟩
  have hloc' : LocalityAEOn (Real.exp κ)
      (XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps ×ˢ B')
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => Pset m₁ ((fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) i)) (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (X1 Gp m₀ j 𝒦X))
      (fun C u u' => agreeOn (N := N) (thickSet Gp (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C))
        u.1 u'.1 ∧ ∀ y ∈ psiThick (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y)
      FF := by
    have e2 : compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (X1 Gp m₀ j 𝒦X) =
        compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) :=
      congrArg (fun S => compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) S) hX₁.symm
    rw [e2]; exact hloc
  obtain ⟨hsum, hlocY, hbound, hanY⟩ := localization_expansion (c := (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)) hcov hd hL hc hcinj hdisj
    hopt hκ₀ hκdec hκ h1 hlog hEb
    (Ag := fun C u u' => agreeOn (N := N) (thickSet Gp (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C))
        u.1 u'.1 ∧ ∀ y ∈ psiThick (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y)
    (AgY := fun Y u u' => agreeOn (N := N) (thickSet Gp Y) u.1 u'.1 ∧
      ∀ y ∈ psiThick Y, u.2 y = u'.2 y) hrefl hlink hana hbd hloc'
  exact ⟨hsum, fun Y u hu u' hu' h1 h2 => hlocY Y u hu u' hu' ⟨h1, h2⟩, hbound, hanY⟩

variable (Gp Hm X₁f) in
/-- **The function of the decoupling parameters expanded by `i5_functional`**: the functional `Φ` of the
decoupled objects `(F₁, Sol)` at the extended parameters, `F(u, s) = Φ(φ_{k+1}(s), δφ(s), u)`. -/
noncomputable def fnOfDec
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ) :
    RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) →
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) → ℂ :=
  fun u s => Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u.1))
    (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
      flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u.1))
        u.1.1 u.2)).1 u

section Fan

variable {Kc Cx c₂ BG₂ δ₁ : ℝ}
variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **`i5_functional` with the term map exposed.** -/
theorem i5_functional_evTerm (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    (hΦbd : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ‖Φ t.1 t.2.1 t.2.2‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {Z Zα : Set (CTorus d L N₁ m₁ K)} (hZ : Z ⊆ ↑X₁f) (hmar : BlockMargin Gp X₁f Zα)
    (hΦloc : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ∀ t' ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Z → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i)) →
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Zα → t.1.2 y = t'.1.2 y) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Z → ∀ i, t.2.1 (y, i) = t'.2.1 (y, i)) →
      agreeOn (thickSet Gp Z) t.2.2.1 t'.2.2.1 → (∀ y ∈ psiThick Z, t.2.2.2 y = t'.2.2.2 y) →
      Φ t.1 t.2.1 t.2.2 = Φ t'.1 t'.2.1 t'.2.2) :
    ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      (∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
        InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
          (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α)) ∧
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ')
          (rawOf D, ψ') =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X), evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
            Gp m₀ (X1 Gp m₀ j 𝒦X) (fnOfDec Gp Hm X₁f F₁ Sol Φ) Y (rawOf D, ψ')) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet Gp Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) (fnOfDec Gp Hm X₁f F₁ Sol Φ) Y u =
        evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) (fnOfDec Gp Hm X₁f F₁ Sol Φ) Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ‖evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) (fnOfDec Gp Hm X₁f F₁ Sol Φ) Y u‖ ≤
          Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ
        (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) (fnOfDec Gp Hm X₁f F₁ Sol Φ) Y)
        (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)) := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  obtain ⟨Sol, hSolan, hSolprop⟩ := Dec2.i4a_analytic (N := N) hC.hS2.fam hC.hS2.an
    hC.SM.toCoverBase hC.hκ.le hC.hM2 false hB0 hC.δ₁_pos.le hC.B_le hC.δ₁_le
  set F : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) →
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) → ℂ :=
    fun u s => Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u.1))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u.1))
          u.1.1 u.2)).1 u with hF'
  have hana := fanF_analytic hC hF₁an hF₁ hSolan hSolprop hΦan
  have hbd : ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
      ∀ s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ)
        (fun _ => Real.exp κ),
      ‖F u s‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X) := by
    rintro ⟨u1, ψ'⟩ ⟨⟨D, hD, rfl⟩, hψ⟩ s hs
    have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
    have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
    have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P‖ < Real.exp κ :=
      norm_extParams_lt hE1 hs'
    obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ := point_facts_core hC hF₁ hSolprop hsx
      (extParams_hs1 (X₁f := X₁f) (Gp := Gp) s) hD hψ
    show ‖Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf D))
          D.Ψ ψ')).1 (rawOf D, ψ')‖ ≤ _
    rw [hFeq, hSeq]
    exact hΦbd _ hmem
  have hloc := fanF_local hC hcov hX₁ hconn hrow hF₁ hSolprop hZ hmar hΦloc
  obtain ⟨hsum, hlocY, hbound, hanY⟩ := expansion_of_AE_evTerm (a₁ := a₁) hC.HBp.hd hC.HBp.hL
    hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb hana hbd hloc
  refine ⟨F₁, Sol, hF₁, fun D hD ψ' hψ => ?_, hlocY, hbound, hanY⟩
  have hsum' := hsum (rawOf D, ψ') ⟨⟨D, hD, rfl⟩, hψ⟩
  rw [show fnOfDec Gp Hm X₁f F₁ Sol Φ = F from rfl, ← hsum']
  symm
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
    fun P => by simpa using hE1
  have hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      (fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) ⟨P, hP⟩ = 1 := fun P hP hPn => rfl
  show Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) 1, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) 1,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) 1, rawOf D))
          D.Ψ ψ')).1 (rawOf D, ψ') = _
  rw [extParams_one]
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core hC hF₁ hSolprop hsx hs1 hD hψ
  rw [hFeq, hSeq]
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  obtain ⟨-, hφ1, hα1⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 le_rfl hδ0' hδ1
    hνε hDom hI
  obtain ⟨hfld, hfix, hs6, -, -, huniq⟩ := hSolprop ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
    flEdat Gp Hm (φ, α) D.Ψ ψ') hsx hstrict
  have hmult := flMult_spec (C := coverOf Gp) (Hm := Hm) (a := compWeight L a₁) (ν := ν)
    (ρ := c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) (s := fun _ : ↥(cubeIdx Gp) => (1 : ℂ))
    (e := flEdat Gp Hm (φ, α) D.Ψ ψ') ⟨hs6, hfix⟩ (fun δα' h => huniq δα' h.1 h.2)
  have hfl : flFieldOne Gp Hm BG₂ κ a₁ ν D ψ' = δφ := by
    have hSol1 : (Sol ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
        flEdat Gp Hm (φ, α) D.Ψ ψ')).1 = δφ := congrArg Prod.fst hSeq
    unfold flFieldOne flField
    rw [hφ1, hα1]
    exact (congrArg (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν
      (fun _ : ↥(cubeIdx Gp) => (1 : ℂ))) (flEdat Gp Hm (φ, α) D.Ψ ψ').2.1
      (flEdat Gp Hm (φ, α) D.Ψ ψ').1 (pertSource Hm (compWeight L a₁)
      (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.1 (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.2)) hmult).trans
      (hfld.symm.trans hSol1)
  rw [hφ1, hα1, hfl]

end Fan

end Core

end Balaban.Localization
