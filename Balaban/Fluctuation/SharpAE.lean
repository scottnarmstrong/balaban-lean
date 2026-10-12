/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatEngineLocalEngine

/-!
# The resummation step with the sharp agreement relation

`AgHatDir hG' Y u u'` says that two data `(Θ, ψ̂)` agree on `Y` in the sharp sense: the raw data
`Θ` agree on the thickening of `Y`, and the hat variables agree at the unit points of the sites
of `Y` itself (not of `blockThick Y`).  It is implied by the landed relation `AgHat`.

The resummation (`expansion_of_AE_hat`) uses of the agreement relation only that it is monotone in
the set and reflexive.  `expansion_of_AE_rel` is the statement for an arbitrary relation with these
two properties; `expansion_of_AE_hat` (landed form, re-derived as a check) and
`expansion_of_AE_hat_dir` (sharp form) are its two instances.  `i5_functional_hat_dir_of_fan` is
`i5_functional_hat` with the fan locality supplied as an explicit hypothesis, in the sharp form.

This file is the resummation step only.  The sharp fan locality itself (needed for the hypothesis
`hfan`) and the four physical summands are separate packages and are not proved here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section SharpAE

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **Sharp agreement of two data `(Θ, ψ̂)` on `Yc`**: the raw data agree on `thickSet Yc` and the
hat variables agree at the unit points of the sites of `Yc` itself. -/
def AgHatDir (hG' : IsLevel Gp (k + 1)) (Yc : Set (CTorus d L N₁ m₁ (k + 1)))
    (u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) : Prop :=
  agreeOn (thickSet Gp Yc) u.1 u'.1 ∧
    ∀ y ∈ Yc, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)

/-- Sharp agreement of two hat variables at the unit points of the sites of `Y`. -/
def AgHatFDir (hG' : IsLevel Gp (k + 1)) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (z z' : unitPts Gp × Fin N → ℂ) : Prop :=
  ∀ y ∈ Y, ∀ i, z (unitPt hG' y, i) = z' (unitPt hG' y, i)

theorem agHatDir_mono (hG' : IsLevel Gp (k + 1)) {Y Y' : Set (CTorus d L N₁ m₁ (k + 1))}
    (h : Y ⊆ Y') {u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)}
    (hu : AgHatDir hG' Y' u u') : AgHatDir hG' Y u u' :=
  ⟨agreeOn_mono (thickSet_mono h) hu.1, fun y hy i => hu.2 y (h hy) i⟩

theorem agHatDir_refl (hG' : IsLevel Gp (k + 1)) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) :
    AgHatDir hG' Y u u :=
  ⟨agreeOn_refl _ u.1, fun _ _ _ => rfl⟩

theorem agHatDir_symm (hG' : IsLevel Gp (k + 1)) {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    {u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)}
    (hu : AgHatDir hG' Y u u') : AgHatDir hG' Y u' u :=
  ⟨fun x hx => ⟨(hu.1 x hx).1.symm, (hu.1 x hx).2.symm⟩, fun y hy i => (hu.2 y hy i).symm⟩

/-- The landed agreement implies the sharp one, since `Y ⊆ psiThick Y ⊆ blockThick Y`. -/
theorem agHatDir_of_agHat (hG' : IsLevel Gp (k + 1)) {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    {u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)}
    (hu : AgHat hG' Y u u') : AgHatDir hG' Y u u' :=
  ⟨hu.1, fun y hy i => hu.2 y (psiThick_subset_blockThick Y (Or.inl hy)) i⟩

theorem agHatFDir_mono (hG' : IsLevel Gp (k + 1)) {Y Y' : Set (CTorus d L N₁ m₁ (k + 1))}
    (h : Y ⊆ Y') {z z' : unitPts Gp × Fin N → ℂ} (hz : AgHatFDir hG' Y' z z') :
    AgHatFDir hG' Y z z' := fun y hy i => hz y (h hy) i

/-- **Lemma AE and the resummation for an arbitrary agreement relation** monotone in the set and
reflexive. -/
theorem expansion_of_AE_rel
    (Ag : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → Prop)
    (hmono : ∀ {Y Y' : Set (CTorus d L N₁ m₁ (k + 1))}, Y ⊆ Y' →
      ∀ {u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)},
        Ag Y' u u' → Ag Y u u')
    (href : ∀ (Y : Set (CTorus d L N₁ m₁ (k + 1)))
      (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)), Ag Y u u)
    (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {B' : Set (unitPts Gp × Fin N → ℂ)}
    {FF : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) →
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) → ℂ}
    (hana : AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts Gp × Fin N → ℂ)) ×
        (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) => FF p.1 p.2)
      ((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B') ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ)))
    (hbd : ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
      ∀ s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ),
      ‖FF u s‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    (hloc : LocalityAEOn (Real.exp κ) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B')
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun C u u' => Ag (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u u') FF) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        FF u 1 = ∑ Y ∈ polymerDomains
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X), Ev Y u) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        Ag Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B')) := by
  classical
  set c : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℕ × CTorus d L N₁ m₁ (k + 1) :=
    fun i => i.1.1 with hcdef
  have hc : ∀ i, c i ∈ cubeIdx Gp := fun i => i.1.2
  have hcinj : Function.Injective c := fun i i' h => Subtype.ext (Subtype.ext h)
  have hdisj : ∀ i, Disjoint (Pset m₁ (c i)) (X1 Gp m₀ j 𝒦X) := fun i => hX₁ ▸ i.2
  have hsub : ∀ C : Finset (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))),
      compY c (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C ⊆
        Ysites Gp m₀ c (X1 Gp m₀ j 𝒦X) C := by
    intro C
    have e1 : compY c (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C =
        compY c (X1 Gp m₀ j 𝒦X) C := congrArg (fun S => compY c S C) hX₁
    rw [e1]; exact compY_subset_Ysites hcov.hU hcov.hN hc _ C
  have hloc' : LocalityAEOn (Real.exp κ)
      (XiCRaw (N := N) Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B')
      (fun i => Pset m₁ (c i)) (compY c (X1 Gp m₀ j 𝒦X))
      (fun C u u' => Ag (compY c (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u u') FF := by
    have e2 : compY c (X1 Gp m₀ j 𝒦X) = compY c (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) :=
      congrArg (fun S => compY c S) hX₁.symm
    rw [e2]; exact hloc
  obtain ⟨hsum, hlocY, hbound, hanY⟩ := localization_expansion (c := c) hcov hd hL hc hcinj hdisj
    hopt hκ₀ hκdec hκ h1 hlog hEb
    (Ag := fun C u u' => Ag (compY c (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u u')
    (AgY := fun Y u u' => Ag Y u u')
    (fun C u _ => href _ u)
    (fun C u u' h => hmono (hsub C) h) hana hbd hloc'
  exact ⟨evTerm c Gp m₀ (X1 Gp m₀ j 𝒦X) FF, hsum,
    fun Y u hu u' hu' h => hlocY Y u hu u' hu' h, hbound, hanY⟩

/-- Sharp form of `expansion_of_AE_hat`: `AgHatDir` in the locality premise and in the
conclusion. -/
theorem expansion_of_AE_hat_dir (hd : 3 ≤ d) (hL : 3 ≤ L) (hG' : IsLevel Gp (k + 1))
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {B' : Set (unitPts Gp × Fin N → ℂ)}
    {FF : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) →
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) → ℂ}
    (hana : AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts Gp × Fin N → ℂ)) ×
        (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) => FF p.1 p.2)
      ((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B') ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ)))
    (hbd : ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
      ∀ s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ),
      ‖FF u s‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    (hloc : LocalityAEOn (Real.exp κ) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B')
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun C u u' => AgHatDir hG' (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u u') FF) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        FF u 1 = ∑ Y ∈ polymerDomains
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X), Ev Y u) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        AgHatDir hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B')) := by
  exact expansion_of_AE_rel (AgHatDir hG') (fun h => agHatDir_mono hG' h)
    (agHatDir_refl hG') hd hL hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb hana hbd hloc

/-- Check: the landed statement of `expansion_of_AE_hat`, re-derived from the generic lemma. -/
theorem expansion_of_AE_hat_via_rel (hd : 3 ≤ d) (hL : 3 ≤ L) (hG' : IsLevel Gp (k + 1))
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {B' : Set (unitPts Gp × Fin N → ℂ)}
    {FF : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) →
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) → ℂ}
    (hana : AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts Gp × Fin N → ℂ)) ×
        (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) => FF p.1 p.2)
      ((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B') ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ)))
    (hbd : ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
      ∀ s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ),
      ‖FF u s‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    (hloc : LocalityAEOn (Real.exp κ) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B')
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun C u u' => AgHat hG' (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u u') FF) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        FF u 1 = ∑ Y ∈ polymerDomains
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X), Ev Y u) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        AgHat hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B')) := by
  exact expansion_of_AE_rel (AgHat hG') (fun h => agHat_mono hG' h)
    (agHat_refl hG') hd hL hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb hana hbd hloc

/-- **Non-vacuity of the sharp premise.**  A functional that, for fixed parameters, depends on the
data only through the hat coordinate at the unit point of a site `y₀ ∈ X₁` (and not on `s`) is
local for `AgHatDir` on the domains `compY c X₁ C`. -/
theorem localityAEOn_coord_dir (hG' : IsLevel Gp (k + 1)) {R : ℝ}
    (S : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)))
    {ι : Type*} [DecidableEq ι] (P : ι → Set (CTorus d L N₁ m₁ (k + 1))) (c : ι → ℕ × CTorus d L N₁ m₁ (k + 1))
    (X₁ : Set (CTorus d L N₁ m₁ (k + 1))) {y₀ : CTorus d L N₁ m₁ (k + 1)} (hy₀ : y₀ ∈ X₁)
    (i₀ : Fin N) :
    LocalityAEOn R S P (compY c X₁)
      (fun C u u' => AgHatDir hG' (compY c X₁ C) u u')
      (fun u _ => u.2 (unitPt hG' y₀, i₀)) := by
  intro C u u' _ _ s s' _ _ _ h
  exact h.2 y₀ (subset_compY (c := c) X₁ C hy₀) i₀

/-- The same functional is local for the landed relation `AgHat`. -/
theorem localityAEOn_coord_hat (hG' : IsLevel Gp (k + 1)) {R : ℝ}
    (S : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)))
    {ι : Type*} [DecidableEq ι] (P : ι → Set (CTorus d L N₁ m₁ (k + 1))) (c : ι → ℕ × CTorus d L N₁ m₁ (k + 1))
    (X₁ : Set (CTorus d L N₁ m₁ (k + 1))) {y₀ : CTorus d L N₁ m₁ (k + 1)} (hy₀ : y₀ ∈ X₁)
    (i₀ : Fin N) :
    LocalityAEOn R S P (compY c X₁)
      (fun C u u' => AgHat hG' (compY c X₁ C) u u')
      (fun u _ => u.2 (unitPt hG' y₀, i₀)) :=
  fun C u u' hu hu' s s' hs hs' hP h =>
    localityAEOn_coord_dir hG' S P c X₁ hy₀ i₀ C u u' hu hu' s s' hs hs' hP (agHatDir_of_agHat hG' h)

/-- The coordinate functional is not constant: two data differing only in the hat coordinate. -/
theorem coord_not_const (hG' : IsLevel Gp (k + 1)) (y₀ : CTorus d L N₁ m₁ (k + 1)) (i₀ : Fin N)
    (r : RawData d L (N₁ * L ^ m₁) (k + 1) N) :
    ∃ u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ),
      u.2 (unitPt hG' y₀, i₀) ≠ u'.2 (unitPt hG' y₀, i₀) :=
  ⟨(r, fun _ => 0), (r, fun _ => 1), by simp⟩

/-- A constant functional is local for both relations. -/
theorem localityAEOn_const_dir (hG' : IsLevel Gp (k + 1)) {R : ℝ}
    (S : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)))
    {ι : Type*} (P : ι → Set (CTorus d L N₁ m₁ (k + 1))) (Yc : Finset ι → Set (CTorus d L N₁ m₁ (k + 1))) (z : ℂ) :
    LocalityAEOn R S P Yc (fun C u u' => AgHatDir hG' (Yc C) u u') (fun _ _ => z) :=
  fun _ _ _ _ _ _ _ _ _ _ _ => rfl

end SharpAE

section SharpFunctional

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **`i5_functional_hat` with the sharp relation and the fan locality as a hypothesis** `hfan`:
for every decoupled background map `F₁` and solution map `Sol` with the properties of
`fanH_local`, the functional built from `Φ` is local for `AgHatDir` on the domains
`compY c X₁ C`.  Everything else is the landed theorem; only the fan-only hypotheses
(`hconn`, `hrow`, `Z`, `Zα`, `hZ`, `hBM`, `hΦloc`) are no longer used. -/
theorem i5_functional_hat_dir_of_fan (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
        (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    (hΦbd : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ‖Φ t.1 t.2.1 t.2.2‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    (hfan : ∀ {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
      (_ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
        InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
          (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
      {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
      (_ : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
        StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
          (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
          Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
          Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
          SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
          (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
            Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)),
      LocalityAEOn (Real.exp κ)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => Pset m₁ i.1.1)
        (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun C u u' => AgHatDir hG' (compY
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u u')
        (fun u s => Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
          (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
            flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
              u.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
                (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
          (u.1, hatPsiF Gp a₁ ν hG' cc F₁
            (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D
            (liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))))
          (rawOf D, liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
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
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hSup : ∀ σ ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ), ∀ D : BgData Gp N,
      XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ ψh ∈ {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) σ)
        (rawOf D) ψh ∈ FlBall Hm δ₁ := by
    intro σ hσ D hD ψh hψh
    have hs' : ∀ i, ‖σ i‖ < Real.exp κ := fun i => by simpa using hσ i
    exact (hatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hF₁
      (norm_extParams_lt hE1 hs') hD hψh).1
  set F : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) →
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) → ℂ :=
    fun u s => Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
          u.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
            (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
      (u.1, hatPsiF Gp a₁ ν hG' cc F₁
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2) with hF'
  have hana := fanH_analytic hC hk hG' cc {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}
    hMX hdm hα hsm hF₁an hF₁ hSolan hSolprop hΦan hSup
  have hbd : ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ),
      ‖F u s‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X) := by
    rintro ⟨u1, ψh⟩ ⟨⟨D, hD, rfl⟩, hψh⟩ s hs
    have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
    have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
      norm_extParams_lt hE1 hs'
    have hψ := hSup s hs D hD ψh hψh
    obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ := point_facts_core hC hF₁ hSolprop hsx
      (extParams_hs1 (X₁f := X₁f) (Gp := Gp) s) hD hψ
    show ‖Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
          D.Ψ (hatPsiF Gp a₁ ν hG' cc F₁
            (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh))).1
      (rawOf D, hatPsiF Gp a₁ ν hG' cc F₁
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh)‖ ≤ _
    rw [hFeq, hSeq]
    exact hΦbd _ hmem
  have hloc := hfan hF₁ hSolprop
  obtain ⟨Ev, hsum, hlocY, hbound, hanY⟩ := expansion_of_AE_hat_dir (a₁ := a₁) hC.HBp.hd hC.HBp.hL
    hG' hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb hana hbd hloc
  refine ⟨Ev, fun D hD ψh hψh => ?_, hlocY, hbound, hanY⟩
  have hsum' := hsum (rawOf D, ψh) ⟨⟨D, hD, rfl⟩, hψh⟩
  rw [← hsum']
  have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
    fun P => by simpa using hE1
  have hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      (fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) ⟨P, hP⟩ = 1 := fun P hP hPn => rfl
  have hψ1 := (hatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hF₁ hsx hD hψh).1
  symm
  show Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1, rawOf D))
          D.Ψ (hatPsiF Gp a₁ ν hG' cc F₁
            (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1) (rawOf D) ψh))).1
      (rawOf D, hatPsiF Gp a₁ ν hG' cc F₁
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1) (rawOf D) ψh) = _
  rw [extParams_one]
  set ψ' := hatPsiF Gp a₁ ν hG' cc F₁ (fun _ => 1) (rawOf D) ψh with hψ'def
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core hC hF₁ hSolprop hsx hs1 hD hψ1
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  obtain ⟨-, hφ1, hα1⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 le_rfl hδ0' hδ1
    hνε hDom hI
  -- the fluctuation field at `s = 1`
  have hψeq : ψ' = liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
      (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
      (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
      (unitQ Gp) (unitP Gp) *ᵥ ψh)) := by
    rw [hψ'def]
    unfold hatPsiF hatSqrtF
    rw [hFeq, extS_one, hφ1, hα1]
    rfl
  rw [← hψeq]
  rw [hFeq, hSeq]
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

end SharpFunctional

end Balaban.Localization
