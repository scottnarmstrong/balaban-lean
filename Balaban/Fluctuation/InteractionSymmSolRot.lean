/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionSymmSol
public import Balaban.Fluctuation.InteractionSymmRot

/-!
# `O(N)` covariance of the expansion terms of a functional of `(φ_{k+1}, δφ, Θ, ψ')`

`Sol_rot`: the fluctuation solution map `Sol` of Theorem I-4a is `O(N)`-covariant:
`Sol (s, (R φ₀, α₀, R δΨ, R f₁)) = (R δφ, δα)`.  `fnOfDecSol_rot` and `evTermSol_rot` give the
`O(N)`-invariance of the function expanded by `i5_functional_evTerm_sol` and of its terms, for a
functional `Φ(φ, α; δφ; u)` that is `O(N)`-invariant.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix
  Balaban.Fluctuation

section Sol

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ : ℝ}

/-- **`O(N)` covariance of the fluctuation solution map** on strict data. -/
theorem Sol_rot
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    {s : Dec2.DecParams (coverOf Gp)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} {α₀ : Hm.Ω 1 → ℂ} {f₁ : Hm.Ω 1 × Fin N → ℂ}
    (he : StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ (φ₀, α₀, δΨ, f₁))
    (he' : StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁
      (DecEquiv.rotSite R φ₀, α₀, DecEquiv.rotSite R δΨ, rotFld R f₁)) :
    Sol (s, (DecEquiv.rotSite R φ₀, α₀, DecEquiv.rotSite R δΨ, rotFld R f₁)) =
      (rotFld R (Sol (s, (φ₀, α₀, δΨ, f₁))).1, (Sol (s, (φ₀, α₀, δΨ, f₁))).2) := by
  obtain ⟨hfld, hfix, hs6, -, -, -⟩ := hSol (s, (φ₀, α₀, δΨ, f₁)) hs he
  obtain ⟨hfld', hfix', hs6', -, -, huniq'⟩ :=
    hSol (s, (DecEquiv.rotSite R φ₀, α₀, DecEquiv.rotSite R δΨ, rotFld R f₁)) hs he'
  simp only at hfld hfix hfld' hfix' huniq'
  have hδ : (Sol (s, (DecEquiv.rotSite R φ₀, α₀, DecEquiv.rotSite R δΨ, rotFld R f₁))).2 =
      (Sol (s, (φ₀, α₀, δΨ, f₁))).2 :=
    (huniq' _ hs6 ((DecEquiv.fluctFixed_rot_iff hR s false α₀ φ₀ δΨ f₁ _).2 hfix)).symm
  refine Prod.ext ?_ hδ
  show (Sol (s, (DecEquiv.rotSite R φ₀, α₀, DecEquiv.rotSite R δΨ, rotFld R f₁))).1 =
    rotFld R (Sol (s, (φ₀, α₀, δΨ, f₁))).1
  rw [hfld', hδ, DecEquiv.fluctField_rot, ← hfld]

end Sol

section Terms

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ K)}
variable {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ K)}

/-- The fluctuation datum of a rotated background is the rotated fluctuation datum. -/
theorem flEdat_rot (R : Matrix (Fin N) (Fin N) ℂ) (φα : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Ψ ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) :
    flEdat Gp Hm (rotFld R φα.1, φα.2) (DecEquiv.rotSite R Ψ) (DecEquiv.rotSite R ψ') =
      (DecEquiv.rotSite R (flEdat Gp Hm φα Ψ ψ').1, (flEdat Gp Hm φα Ψ ψ').2.1,
        DecEquiv.rotSite R (flEdat Gp Hm φα Ψ ψ').2.2.1, rotFld R (flEdat Gp Hm φα Ψ ψ').2.2.2) := by
  classical
  unfold flEdat
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl ?_))
  · funext x i
    simp only [barField, DecEquiv.rotSite, Matrix.mulVec, dotProduct]
    by_cases h : x ∈ Gp.Ω 1
    · simp [h, rotFld]
    · simp [h]
  · funext p
    simp [rotFld]

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **The function expanded for a functional of `(φ_{k+1}, α_{k+1}, δφ, u)` is `O(N)`-invariant**
on the polydisc. -/
theorem fnOfDecSol_rot
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) δφ u,
      Φ (rotFld (cmat Q) bg.1, bg.2) (rotFld (cmat Q) δφ) (rotU (cmat Q) u) = Φ bg δφ u)
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)
    {s : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ}
    (hs : s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ)
      (fun _ => Real.exp κ)) :
    fnOfDec Gp Hm X₁f F₁ Sol Φ (rotU (cmat Q) u) s = fnOfDec Gp Hm X₁f F₁ Sol Φ u s := by
  have hu' := rotU_mem (Gp := Gp) (Hm := Hm) (a₁ := a₁) (ν := ν) (eps := eps) (δ₁ := δ₁) hQ hu
  obtain ⟨⟨D, hD, hDu⟩, hψ⟩ := hu
  obtain ⟨u1, ψ'⟩ := u
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  have hDu' : u1 = rawOf D := hDu
  subst hDu'
  have hR : (cmat Q)ᵀ * cmat Q = 1 := (isRealOrth_ofReal hQ).1
  have hψ' : (fun x => cmat Q *ᵥ ψ' x) ∈ FlBall Hm δ₁ := hu'.2
  have hD' := xiCData_rot hQ hD
  obtain ⟨φ, α, δφ, δα, hI, hF, hstr, hS, -⟩ := point_facts_core hC hF₁ hSol hsx hs1 hD hψ
  obtain ⟨φ', α', δφ', δα', hI', hF', hstr', hS', -⟩ :=
    point_facts_core hC hF₁ hSol hsx hs1 hD' hψ'
  have hrot := F₁_rot hC hF₁ hsx hD hQ
  have hF'' : F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rotRaw (cmat Q) (rawOf D)) =
      (rotFld (cmat Q) φ, α) := by rw [hrot, hF]
  have hF3 : F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf (D.rot (cmat Q))) =
      (φ', α') := hF'
  have hpa : (φ', α') = (rotFld (cmat Q) φ, α) := by rw [← hF3]; exact hF''
  obtain ⟨h1, h2⟩ := Prod.mk.inj hpa
  subst φ'
  subst α'
  have hE := flEdat_rot (Gp := Gp) (Hm := Hm) (cmat Q) (φ, α) D.Ψ ψ'
  have hSolr := Sol_rot hSol hR hsx
    (φ₀ := (flEdat Gp Hm (φ, α) D.Ψ ψ').1) (α₀ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.1)
    (δΨ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.1) (f₁ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.2)
    hstr (by rw [← hE]; exact hstr')
  unfold fnOfDec
  show Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rotRaw (cmat Q) (rawOf D)))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
          rotRaw (cmat Q) (rawOf D))) (rotRaw (cmat Q) (rawOf D)).1 (rotU (cmat Q) (rawOf D, ψ')).2)).1
      (rotU (cmat Q) (rawOf D, ψ')) = _
  rw [hF'']
  show Φ _ (Sol (_, flEdat Gp Hm (rotFld (cmat Q) φ, α) (DecEquiv.rotSite (cmat Q) D.Ψ)
    (DecEquiv.rotSite (cmat Q) ψ'))).1 _ = _
  rw [hE, hSolr]
  show _ = Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf D))
    (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
      flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf D)) D.Ψ ψ')).1
    (rawOf D, ψ')
  rw [hF]
  exact hΦ (φ, α) _ (rawOf D, ψ')

/-- **The expansion terms of a functional of `(φ_{k+1}, α_{k+1}, δφ, u)` inherit its
`O(N)`-invariance**: `𝓔(X, Y)(R u) = 𝓔(X, Y)(u)` whenever
`Φ(R φ, α; R δφ; R u) = Φ(φ, α; δφ; u)`. -/
theorem evTermSol_rot
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) δφ u,
      Φ (rotFld (cmat Q) bg.1, bg.2) (rotFld (cmat Q) δφ) (rotU (cmat Q) u) = Φ bg δφ u)
    (Y : Set (CTorus d L N₁ m₁ K))
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) :
    evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ X₁
        (fnOfDec Gp Hm X₁f F₁ Sol Φ) Y (rotU (cmat Q) u) =
      evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ X₁
        (fnOfDec Gp Hm X₁f F₁ Sol Φ) Y u :=
  evTerm_congr_polydisc _ (Real.one_lt_exp_iff.2 hC.hκ) X₁ Y
    fun _ hs => fnOfDecSol_rot hC hF₁ hSol hQ hΦ hu hs

end Terms

end Balaban.Localization
