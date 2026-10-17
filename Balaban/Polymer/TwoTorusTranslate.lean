/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapScales
public import Balaban.Fluctuation.InteractionSymmLat
public import Balaban.Localization.DecEquivTranslatePolymer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Translation covariance of the step terms by cell-aligned translations

The paving symmetries of the landed covariance (`pavingSymGroup`, the lattice symmetries
`LatSymm.ofTranslateLevel`, `CoverSymm.ofTranslate`, `BlockSymm.ofTranslate`,
`PolymerSymm.ofTranslate`) contain every translation `x ↦ x + t` of the step torus by a vector `t`
with `L ^ (n + m₀ + m₁) ∣ t_μ` for all `μ` (`n` the level of the top generating set, so
`L ^ (n + m₀ + m₁)` is the cell side `a_n`), provided `L ^ m₀ ∣ N₁`.

* `evTerm_translate_step`: the expansion term of the step function of a background functional is
  invariant under such a translation, `𝓔(X + t, Y + t)(τ_t u) = 𝓔(X, Y)(u)`; it is the landed
  `evTerm_sym` at `σ = x ↦ x + t`.
* `evTerm_translate_aligned`: the same for an arbitrary function of the cut parameters that is
  transported by the relabelling of the parameters.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section Cov

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ n : ℕ}

/-- **Translation covariance of the step terms** (item 24, part 1).  Let `Gp` be a level set
of level `n`, `Sm`, `S` the translation lattice symmetries of `Hm`, `Gp` (`LatSymm.ofTranslateLevel`), `L ^ m₀ ∣ N₁`, and `t` a translation of the torus with
`L ^ (n + m₀ + m₁) ∣ t_μ` (a multiple of the cell side `a_n`).  Then
`𝓔(X + t, Y + t)(τ_t u) = 𝓔(X, Y)(u)` for the expansion terms of the step function of a
background functional which is invariant under the translation (`hΦ`); this is `evTerm_sym` at
`σ = x ↦ x + t`, whose lattice, cover, block and polymer symmetries are the translation ones. -/
theorem evTerm_translate_step
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hGp : IsLevel Gp n) (hN : L ^ m₀ ∣ N₁)
    (t : CTorus d L N₁ m₁ K) (ht : ∀ μ, L ^ (n + m₀ + m₁) ∣ (t μ).val)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol Sol' : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (S : LatSymm Gp Gp (Equiv.addRight t)) (Sm : LatSymm Hm Hm (Equiv.addRight t))
    {X₁f X₁f' : Finset (CTorus d L N₁ m₁ K)}
    (hX : (↑X₁f' : Set (CTorus d L N₁ m₁ K)) =
      (Equiv.addRight t) '' (↑X₁f : Set (CTorus d L N₁ m₁ K)))
    {Φb : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) u,
      Φb (S.fld bg.1, S.mul bg.2) (symU (Equiv.addRight t) u) = Φb bg u)
    (hana : AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
          (CTorus d L N₁ m₁ K → Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
        fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u) p.1 p.2)
        ((XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) ×ˢ
          polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ)))
    (hana' : AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
          (CTorus d L N₁ m₁ K → Fin N → ℂ)) × (ParIdx Gp (↑X₁f' : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
        fnOfDec Gp Hm X₁f' F₁ Sol' (fun bg _ u => Φb bg u) p.1 p.2)
        ((XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) ×ˢ
          polydisc (0 : ParIdx Gp (↑X₁f' : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ)))
    (X₁ Y : Set (CTorus d L N₁ m₁ K))
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) :
    evTerm (fun i : ParIdx Gp (↑X₁f' : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
        ((Equiv.addRight t) '' X₁)
        (fnOfDec Gp Hm X₁f' F₁ Sol' (fun bg _ u => Φb bg u)) ((Equiv.addRight t) '' Y)
        (symU (Equiv.addRight t) u) =
      evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ X₁
        (fnOfDec Gp Hm X₁f F₁ Sol (fun bg _ u => Φb bg u)) Y u := by
  have ht1 : ∀ μ, L ^ (n + m₁) ∣ (t μ).val := fun μ =>
    (pow_dvd_pow L (by omega)).trans (ht μ)
  exact evTerm_sym hC hF₁ S Sm
    (DecEquiv.CoverSymm.ofTranslate hGp t ht1)
    (DecEquiv.BlockSymm.ofTranslate hGp t (fun μ => (pow_dvd_pow L (by omega)).trans (ht μ)))
    (DecEquiv.PolymerSymm.ofTranslate hGp hN t ht) hX hΦ hana hana' X₁ Y hu

/-- **Translation covariance of the expansion terms of an arbitrary function of the cut
parameters**: if `F' u'` is `F u` composed with the relabelling `parEquiv` of the parameters at the
points of the unit polydisc, then `𝓔(X + t, Y + t)(F') = 𝓔(X, Y)(F)`, for `t` a multiple of the
cell side `a_n`. -/
theorem evTerm_translate_aligned {R : ℝ} (hR : 1 < R)
    (hGp : IsLevel Gp n) (hN : L ^ m₀ ∣ N₁)
    (t : CTorus d L N₁ m₁ K) (ht : ∀ μ, L ^ (n + m₀ + m₁) ∣ (t μ).val)
    (S : LatSymm Gp Gp (Equiv.addRight t))
    {X₁' : Set (CTorus d L N₁ m₁ K)} (X₁ Y : Set (CTorus d L N₁ m₁ K))
    (hX : X₁' = (Equiv.addRight t) '' X₁)
    {U U' : Type*} {F : U → (ParIdx Gp X₁ → ℂ) → ℂ} {F' : U' → (ParIdx Gp X₁' → ℂ) → ℂ}
    {u : U} {u' : U'}
    (hF : AnalyticOnNhd ℂ (F u) (polydisc (0 : ParIdx Gp X₁ → ℂ) (fun _ => R)))
    (hF' : AnalyticOnNhd ℂ (F' u') (polydisc (0 : ParIdx Gp X₁' → ℂ) (fun _ => R)))
    (hff : ∀ s ∈ unitCube (ParIdx Gp X₁'), F' u' s = F u (s ∘ parEquiv
      (DecEquiv.CoverSymm.ofTranslate hGp t (fun μ => (pow_dvd_pow L (by omega)).trans (ht μ)))
      (DecEquiv.PolymerSymm.ofTranslate hGp hN t ht) hX)) :
    evTerm (fun i : ParIdx Gp X₁' => i.1.1) Gp m₀ ((Equiv.addRight t) '' X₁) F'
        ((Equiv.addRight t) '' Y) u' =
      evTerm (fun i : ParIdx Gp X₁ => i.1.1) Gp m₀ X₁ F Y u :=
  evTerm_relabel (fun i : ParIdx Gp X₁ => i.1.1) (fun i : ParIdx Gp X₁' => i.1.1) _ hR
    (DecEquiv.PolymerSymm.ofTranslate hGp hN t ht) S (fun _ => rfl) (fun i => i.1.2) X₁ Y hF hF'
    hff

end Cov

end Balaban.Polymer.TwoTorusStep
